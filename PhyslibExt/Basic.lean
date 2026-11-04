/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Physlib.SpaceAndTime.Space.Basic

/-!
# PhyslibExt bootstrap

An import-only entry point for the upstream Physlib dependency.

## i. Overview

This module exposes Physlib's `Space` API without copying its definitions or
adding a parallel representation. Physics developments should import the
specific upstream and extension modules they use.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Upstream API

## iv. References

- `Physlib.SpaceAndTime.Space.Basic` in
  https://github.com/leanprover-community/physlib at the root package's pin

## A. Upstream API

The public import supplies upstream `Space` and its affine and metric APIs.
The companion test checks them through this extension-library entry point.
-/
