# Contributing to ATLAS

We want to make contributing to this project as easy and transparent as
possible.

## Our Development Process
... (in particular how this is synced with internal changes to the project)

## Picking a task

The [site](https://facebookresearch.github.io/atlas-lean/) lists the
formalization tasks that are ready now: statements to write in Lean and
statements to prove, as `autoform work` finds them
([What the tools own](docs/BLUEPRINT.md#what-the-tools-own)). It publishes
them as
[`tasks.json`](https://facebookresearch.github.io/atlas-lean/tasks.json), which
each `main` build writes with `autoform work list --json`, together with the
commit it was computed from. You don't need to build the repository to pick
one, and people and agents follow the same steps:

1. Take a task from `tasks.json`. `python3 scripts/next_task.py` prints the
   next ones; `--json` prints them for agents.
2. Skip a task that an open pull request names, by its article id (`af_…`) or
   its Lean declaration, in its title, body or branch. `next_task.py` skips
   those, including those an older pull request names, in its title, branch or
   code, by the end of a declaration's name that no other task shares, and the
   tasks of pull requests merged into `main` since `tasks.json` was computed.
3. Open a draft pull request early, with the task's article id in its body, so
   that others see the task is taken. Mark it ready for review when it is done,
   or close it if you stop.

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

File contents, commit messages (not headers), the message of a supported
embedded merge tag, and PR titles and descriptions recognize two public forms;
filenames, branches, header values, and symlink targets stay strict. A whole
recognized form must lie inside one such message. A publisher identifier is
exempt only in the exact identifier slot of a recognized citation: a DOI under
a listed publisher prefix (optionally prefixed by `doi:` or
`https://doi.org/`) with a valid ISSN check digit, a recognized ScienceDirect
article URL, or an exact citation in the checker.

A filesystem-path match wholly inside an HTTP(S) URL path is exempt only for
a public-looking DNS authority with no user information, valid labels and
port syntax, no local or special-use suffix, and no drive-letter path segment.
Local names, IP literals, and malformed authorities stay strict. A control
character (C0, DEL, or C1) ends the URL path, so text after one is checked.
Other rules still apply inside the URL, and query and fragment text remains
checked.
The checker does not resolve DNS, so a public-looking name is not proof that
its destination is public. New citation forms need a reviewed base-checker
change. These exceptions do not waive other findings or missing inputs.

The **Public references / public-references** check applies to every PR author,
including forks. It reads every outgoing Git commit's complete message and all
headers, including signature-shaped text, plus every new Git file blob. File
versions replaced or deleted before the tip are included. Signature markers
never disable scanning; they are data, not authenticated signatures. File
contents the current base or a public tip still holds, as a file or as a
symlink target, are not re-scanned as file contents; a new or changed symlink
target is scanned strictly, even when its bytes are held as file text. A
single-parent commit that only makes a base-history file executable, with the
same path and bytes, does not have them re-scanned; that skip never counts as a
scan for later commits. New destination filenames are still checked. Editing the
contents or mode of an existing path does not re-report its name. In a merge, a
base-side parent is a direct parent reachable from the base and not contained
in another parent. A name is not re-reported when the current base, a public
tip, or a base-side parent has that exact path, even if the merge changes its
contents or mode.
File contents are scanned unless the current base or a public tip holds the
same bytes (at any path), the merge keeps a base-side parent's exact entry
(same path, mode, and object), or they were already scanned. A retained
symlink target is scanned strictly unless the current base or a public tip
holds it as a symlink target, the merge keeps such an exact entry, or it was
already scanned as a target; a new or changed target is always strict. A
base-side parent's bytes at another path never count. So contents and symlink
targets a merge brings back after the base removed or cleaned them are checked
again, and so is a restored name absent from every base-side parent. The commit
graph cannot tell a deliberate same-path import from an earlier ordinary merge
of a base-side parent, so that parent's exact path and exact entry still pass.
Submodule entries pass only when kept unchanged from the current base or a
public tip. Existing historical
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

### Graph PRs

A graph PR changes the ATLAS wiki; its content follows the
[graph rules](docs/BLUEPRINT.md#graph-rules).

- **Keep it under 3,000 changed files and name its issue** (`Closes #…` or
  `Part of #…`). GitHub shows at most 3,000 files in one diff.
- **An expansion changes no Lean outside `WantedExt`,** so its reviewer need
  not also review proofs.
- **Leave what the tools own alone** ([What the tools
  own](docs/BLUEPRINT.md#what-the-tools-own)).
- **A code owner approves it** (`.github/CODEOWNERS`) **and Codex reviews it:**
  automatically for the repository's owners, members and collaborators and for
  forks on `codex.yml`'s trusted list; on any other fork PR a maintainer
  comments `@codex` for an advisory review. Agents produce graph changes faster
  than people can check them, and a poor expansion spreads into every task
  below it.

## How PRs merge

`main` takes changes through GitHub's merge queue; do not push to it directly.
When a PR is ready to merge and its required checks have passed, add it to the
queue. The queue tests it on top of the current `main` and the PRs queued ahead
of it, and squash-merges it only if the required checks pass on that combined
tree, so each commit it adds to `main` has passed them on its own tree.

To queue a PR, use one of:

- **Merge when ready** in the PR's merge box.
- `gh pr merge <number>`, with `--match-head-commit <sha>` to queue only the
  commit you checked. It queues the PR at once if its required checks have
  passed; otherwise it turns on auto-merge, which queues the PR when they pass.
  The queue sets the merge method and the commit message, so `--squash`,
  `--subject` and `--body` have no effect, and `gh` refuses `--delete-branch`.
- The GraphQL mutation `enqueuePullRequest` (`pullRequestId`, and
  `expectedHeadOid` to pin the head). It queues the PR only if it can be queued
  now; otherwise it returns an error that says why.

The REST endpoint `PUT /repos/{owner}/{repo}/pulls/{number}/merge` does not
support merge queues, so it stops working for `main` once the queue is
required. Scripts and bots that merge with it must switch to `gh pr merge`,
`enqueuePullRequest`, or `PUT /repos/{owner}/{repo}/pulls/{number}/merge-async`
with `"merge_action": "merge_queue"`. Each of these only queues the PR: read the
PR's state afterwards to learn whether it merged or left the queue.

The queue removes a PR whose required checks fail on its merge group, or do not
report before the queue's timeout; the PR's timeline says why, and the PRs
behind it rebuild without it. Fix the PR and queue it again. To take a PR out
of the queue, use **Remove from queue** on the PR or on the queue's page, or the
GraphQL mutation `dequeuePullRequest`; `gh` cannot do it.

### Required checks

A PR needs these checks to pass before it can be queued, and again on its merge
group before it merges:

- `repository integrity` (CI): the deterministic repository checks.
- `build` (CI): the Lean build and its policy checks.
- `source-diagnostics` (Source diagnostics).
- `guard` (Bump guard): the Lean and Mathlib pin check. On a merge group it
  checks a pin change again against the queue's base.

Each of them runs on every PR and every merge group;
`scripts/test_merge_queue_checks.py`, run by `scripts/check.sh preflight`,
fails if a change would stop that. The other checks are advisory. Codex runs on
PR events only. `public-references` runs on PRs and merge groups, but stays
advisory until the workflow governance described under
[Public references](#public-references) is in place. Blueprint Pages, Check
workflows and Binary64 conformance run only on PRs that touch their files, and
Blueprint Pages also builds `main` once a day.

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
