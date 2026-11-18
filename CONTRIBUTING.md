# Contributing to ATLAS

We want to make contributing to this project as easy and transparent as
possible.

## Our Development Process
... (in particular how this is synced with internal changes to the project)

## Pull Requests
We actively welcome your pull requests.

1. Fork the repo and create your branch from `main`.
2. If you've added code that should be tested, add tests.
3. If you've changed APIs, update the documentation.
4. Ensure the test suite passes.
5. Make sure your code lints.
6. If you haven't already, complete the Contributor License Agreement ("CLA").

### Public references

Files, filenames, branch names, PR titles/descriptions, and complete commit
messages must not contain private task/diff/paste identifiers, private service
links, machine names, or personal workspace paths. Keep private provenance in
private records; use public citations and repository-relative paths here.
Host-path checks accept either slash convention, including doubled backslashes
in string literals and Windows profile-directory casing. Conventional CI
account names `runner` and `runneradmin` are excluded; longer profile names
that start with either word are not. Profile names may contain apostrophes or
Unicode spaces; finding the profile directory is enough to report the path.
A quote immediately after a root is treated as a text boundary, and profile
matches do not cross line breaks. When a path is wrapped in matching double
quotes, single quotes, or backticks, and in filenames, symlink targets, branch
names, and commit header values (identity names included), a profile name that ends the path runs to the closing quote or
the end of the value: only the exact CI account names, an empty name, `.`, and
`..` are exempt there, so `runner!` or `runner.` is reported. In unquoted
prose, sentence punctuation after a root or an exact CI account name is treated
as prose; this is a finite heuristic, not a parser for every file name.
The numeric-reference and campaign-code checks ignore letter case in branch
names and treat underscores as separators. Slashes remain path boundaries;
compound campaign/lesson references have a separate slash-aware pattern, also
checked case-insensitively when quoted in PR text or files.
Dotted roadmap-label checks use the original case and require at least four
upper-case parts; three-part package names and lower-case release branches are
not classified by that shape alone.
Preserve authorship and copyright notices when correcting provenance.

File contents, commit messages (not headers), and PR titles and descriptions
recognize two public forms; filenames, branches, and symlink targets stay
strict. A publisher identifier is exempt only in the exact identifier slot of
a recognized citation: a DOI under a listed publisher prefix (optionally
prefixed by `doi:` or `https://doi.org/`) with a valid ISSN check digit, a
recognized ScienceDirect article URL, or an exact citation in the checker.

A filesystem-path match wholly inside an HTTP(S) URL path is exempt only for
a public-looking DNS authority with no user information, valid labels and
port syntax, no local or special-use suffix, and no drive-letter path segment.
Local names, IP literals, and malformed authorities stay strict. Other rules
still apply inside the URL, and query and fragment text remains checked.
The checker does not resolve DNS, so a public-looking name is not proof that
its destination is public. New citation forms need a reviewed base-checker
change. These exceptions do not waive other findings or missing inputs.

The **Public references / public-references** check applies to every PR author,
including forks. It reads every outgoing Git commit's complete message and all
headers, including signature-shaped text, plus every new Git file blob. File
versions replaced or deleted before the tip are included. Signature markers
never disable scanning; they are data, not authenticated signatures. Blob
contents Git excludes as base-history objects are not re-scanned; new
destination filenames are still checked. A merge does not re-report a filename
inherited unchanged from a parent: its origin is checked in the outgoing
ancestor commits, or excluded with the base history. Deliberately restored
historical files can be introduced and checked again. Existing historical
exposures need separate cleanup. It does not
only inspect subjects or added lines. Errors, missing objects, moved PR
metadata, and incomplete ranges fail
the check. It never executes code from the proposed head. PR description edits
rerun it too. LFS pointers, including CRLF and legacy-version forms, fail because
their external contents are not scanned.

Reports contain at most 100 findings, with locations limited to 240 characters.
`findings_truncated: true` means additional findings were omitted. After the
limit is exceeded, reference detection stops, but object and input-completeness
validation continues. A truncated report always fails the check.

To check a local branch before its first push, fetch the public base and scan
its full outgoing range. Put the intended branch name in `pr-metadata.json`
under `branch`; include `title` and `body` if you will also create a PR:

```sh
git fetch origin &&
python3 scripts/check_public_references.py \
  --base "$(git rev-parse origin/main)" --head "$(git rev-parse HEAD)" \
  --metadata pr-metadata.json
```

For an update to an existing public branch, also exclude its already-published
tip. Replace `my-branch` with the remote branch name:

```sh
git fetch origin &&
python3 scripts/check_public_references.py \
  --base "$(git rev-parse origin/main)" --head "$(git rev-parse HEAD)" \
  --public "$(git rev-parse origin/main)" \
  --public "$(git rev-parse origin/my-branch)"
```

`--public` takes a full commit SHA and may be repeated. It excludes published
commit histories, but only entries in each public tip's current tree qualify
for its content and name exemptions. Editing a file under an existing public
name does not force a rename. Removed names, symlinks, and content are checked
again when a push restores them, directly, through a merge, or by building on
an older public commit. New symlink targets are always checked strictly. The
normal base-history behavior is unchanged. This supports forward cleanup,
including updates that merge already-public main and topic tips.

Only pass tips you have fetched from the public repository and verified: the
script checks that each value identifies a commit, not that it is public.
Leave `--public` out for a first push. New outgoing commit headers and
messages, introduced file blobs, new destination paths, and new symlink
targets remain checked.

`--public` excludes Git history only. If you are also creating or changing PR
metadata or a branch name, pass the exact new `title`, `body`, or `branch`
values in a JSON file with `--metadata pr-metadata.json`; supplied fields are
always checked. Unchanged, already-public metadata need not be supplied for
a code-only local pre-push check. The GitHub PR check does not accept
`--public` and still scans the PR's complete range from its base; merge-group
checks likewise remain unchanged. A local pass does not waive a CI finding
or authorize rewriting published history to remove it.

Run the detector's tests with:

```sh
python3 -m unittest discover -s scripts -p 'test_public_references.py'
```

The detector uses identifier/URL/path patterns, not a list of confidential model
names. It is a backstop, not a confidentiality guarantee: unfamiliar private
references, encoded data, images, and compressed archive contents need author
review. Binary files receive a raw-byte text scan, not decompression or OCR.
Legitimate public identifiers can collide with the patterns. In particular,
hyphenated or underscored F-number topics can have the same shape as private
work-item codes. A finding is not proof that the identifier is confidential;
ask maintainers to review such a case rather than disguising the text or
disabling the check. A review accept alone does not change a failing check.
Removing a reference from the tip does not erase already-published history.
CI runs after a branch and PR have been published; run the local check before
pushing to avoid exposing a reference in the first place.

The same job also handles merge-queue events, scanning the complete combined
Git range, including intermediate commits, without executing proposed code.
It pins scanner code to a resolved default-branch commit and checks the queue
ref before and after scanning. PR metadata is checked separately on PR events;
the merge-group route does not enumerate every grouped PR's metadata.

Before making this check required, maintainers must establish trusted workflow
governance. GitHub selects a merge-group workflow definition from the event
ref, and a PR-target workflow from the PR's base branch. Pinning the scanner
does not authenticate the workflow that invokes it. Use a required workflow
from a separately protected source, or enforce trusted review and protection
for all workflow definitions, relevant policy, and default-branch scanner
code. A required job name alone cannot prevent another workflow from reporting
the same name. Verify ordinary PR, fork, and merge-queue delivery after an
authorized deployment before enabling required enforcement. Until then this
is advisory CI, not a standalone merge barrier.

## Contributor License Agreement ("CLA")
In order to accept your pull request, we need you to submit a CLA. You only need
to do this once to work on any of Meta's open source projects.

Complete your CLA here: <https://code.facebook.com/cla>

## Issues
We use GitHub issues to track public bugs. Please ensure your description is
clear and has sufficient instructions to be able to reproduce the issue.

Meta has a [bounty program](https://bugbounty.meta.com/) for the safe
disclosure of security bugs. In those cases, please go through the process
outlined on that page and do not file a public issue.

## Coding Style
* 2 spaces for indentation rather than tabs
* 80 character line length
* ...

## Copyright headers
Every Lean file starts with the Meta header:

```lean
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
```

Code from another project keeps that project's copyright notice:

* A file that is mostly copied from another project starts with that project's
  copyright and license header instead (for example, the Apache 2.0 header of
  Formal Conjectures, or the header of the Mathlib file it copies).
* A mostly original file that adapts code from another project keeps the Meta
  header and adds a second block naming each source file, its copyright holder,
  license and authors, for the adapted portions only:

```lean
/-
Portions of this file are adapted from:

`Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean` (Mathlib):
Copyright (c) 2018 Chris Hughes. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
```

CI checks every tracked Lean file with `scripts/check_copyright.py --all` (part of
`scripts/check.sh preflight`); `scripts/check_copyright.py --fix FILE...` adds the
Meta header to files that have none.

## License
By contributing to ATLAS, you agree that your contributions will be licensed
under the LICENSE file in the root directory of this source tree.
