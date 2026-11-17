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
Branch identifier checks ignore letter case and treat underscores as separators.
Preserve authorship and copyright notices when correcting provenance.

The **Public references / public-references** check applies to every PR author,
including forks. It reads every outgoing Git commit's message and identity
headers and every new Git file blob introduced by those commits, including
versions replaced or deleted before the tip. Content already reachable from
the base's history is not re-scanned; copying it still checks the destination
filename. Existing historical exposures need separate cleanup. It does not
only inspect subjects or added lines. Errors, missing objects, moved PR
metadata, and incomplete ranges fail
the check. It never executes code from the proposed head. PR description edits
rerun it too. LFS pointers, including CRLF and legacy-version forms, fail because
their external contents are not scanned.

Reports contain at most 100 findings, with locations limited to 240 characters.
`findings_truncated: true` means additional findings were omitted. After the
limit is exceeded, reference detection stops, but object and input-completeness
validation continues. A truncated report always fails the check.

To check a local branch before pushing, with optional JSON containing `title`,
`body`, and `branch` fields:

```sh
python3 scripts/check_public_references.py \
  --base "$(git rev-parse origin/main)" --head "$(git rev-parse HEAD)" \
  --metadata pr-metadata.json
python3 -m unittest discover -s scripts -p 'test_public_references.py'
```

The detector uses identifier/URL/path patterns, not a list of confidential model
names. It is a backstop, not a confidentiality guarantee: unfamiliar private
references, encoded data, images, and compressed archive contents need author
review. Binary files receive a raw-byte text scan, not decompression or OCR.
Legitimate public identifiers can collide with the patterns; ask maintainers to
review such a case rather than disguising the text or disabling the check.
Removing a reference from the tip does not erase already-published history.
CI runs after a branch and PR have been published; run the local check before
pushing to avoid exposing a reference in the first place.

Maintainers must make `public-references` a required check in the branch ruleset
after this workflow lands. Until it is required, CI reports failures but does
not itself prevent a manual merge. The workflow runs the trusted default-branch
version, so changes to the gate itself need maintainer review and local tests before
merge; a PR cannot substitute its own scanner into this check.

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
