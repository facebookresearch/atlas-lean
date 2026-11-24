/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorFlat
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorNested
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorUnit

/-!
# Comparisons of the original enriched Day associator presentations

The nested coend comparisons retain their original projection legs and
complete relations. The flattened triple comparison retains the actual
index and coefficient associators in both directions.
-/
