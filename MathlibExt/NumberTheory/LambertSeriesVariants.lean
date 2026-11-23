/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Terms of the Lambert-type series $\tilde L_m$.** For a complex number $q$ with $|q| < 1$,
an integer $m \ge 1$ and a natural number $k$, the term of index $k$ is
$q^{(2k+1)m} / (1 + q^{2k+1})^{2m}$, that is, $q^{(2n-1)m} / (1 + q^{2n-1})^{2m}$ with $n = k + 1$.

Source: Gerhold, concept `jis_sem_e9cabece6d32bf6b52d62673`,
source `jis_f199df27bfb37c3d9b045e32`. -/
noncomputable def tildeLMSummand (q : { q : ℂ // ‖q‖ < 1 }) (m : { m : ℕ // 1 ≤ m }) (k : ℕ) : ℂ :=
  (q.val ^ ((2 * k + 1) * m.val)) / ((1 + q.val ^ (2 * k + 1)) ^ (2 * m.val))

/-- **Summability of the Lambert-type series $\tilde L_m$.** For a complex number $q$ with
$|q| < 1$ and an integer $m \ge 1$, this predicate holds when the series
$\sum_{n \ge 1} q^{(2n-1)m} / (1 + q^{2n-1})^{2m}$ is summable in $\mathbb{C}$.

Source: Gerhold, concept `jis_sem_e9cabece6d32bf6b52d62673`,
source `jis_f199df27bfb37c3d9b045e32`. -/
noncomputable def tildeLMSummable (q : { q : ℂ // ‖q‖ < 1 }) (m : { m : ℕ // 1 ≤ m }) : Prop :=
  Summable (tildeLMSummand q m)

/-- **The Lambert-type series $\tilde L_m$.** For a complex number $q$ with $|q| < 1$ and an
integer $m \ge 1$, $\tilde L_m(q) = \sum_{n \ge 1} q^{(2n-1)m} / (1 + q^{2n-1})^{2m}$, where the
sum is taken to be $0$ if the series is not summable.

Source: Gerhold, concept `jis_sem_e9cabece6d32bf6b52d62673`,
source `jis_f199df27bfb37c3d9b045e32`. -/
noncomputable def tildeLM (q : { q : ℂ // ‖q‖ < 1 }) (m : { m : ℕ // 1 ≤ m }) : ℂ :=
  tsum (tildeLMSummand q m)

/-- **Terms of the Lambert-type series $\hat L_m$.** For a complex number $q$ with $|q| < 1$,
an integer $m \ge 1$ and a natural number $k$, the term of index $k$ is
$q^{m(k+1)} / (1 + q^{2(k+1)})^m$, that is, $q^{mn} / (1 + q^{2n})^m$ with $n = k + 1$.

Source: Gerhold, concept `jis_sem_e9cabece6d32bf6b52d62673`,
source `jis_f69070cf1636bd79774e81a9`. -/
noncomputable def hatLMSummand (q : { q : ℂ // ‖q‖ < 1 }) (m : { m : ℕ // 1 ≤ m }) (k : ℕ) : ℂ :=
  (q.val ^ (m.val * (k + 1))) / ((1 + q.val ^ (2 * (k + 1))) ^ m.val)

/-- **Summability of the Lambert-type series $\hat L_m$.** For a complex number $q$ with
$|q| < 1$ and an integer $m \ge 1$, this predicate holds when the series
$\sum_{n \ge 1} q^{mn} / (1 + q^{2n})^m$ is summable in $\mathbb{C}$.

Source: Gerhold, concept `jis_sem_e9cabece6d32bf6b52d62673`,
source `jis_f69070cf1636bd79774e81a9`. -/
noncomputable def hatLMSummable (q : { q : ℂ // ‖q‖ < 1 }) (m : { m : ℕ // 1 ≤ m }) : Prop :=
  Summable (hatLMSummand q m)

/-- **The Lambert-type series $\hat L_m$.** For a complex number $q$ with $|q| < 1$ and an
integer $m \ge 1$, $\hat L_m(q) = \sum_{n \ge 1} q^{mn} / (1 + q^{2n})^m$, where the sum is
taken to be $0$ if the series is not summable.

Source: Gerhold, concept `jis_sem_e9cabece6d32bf6b52d62673`,
source `jis_f69070cf1636bd79774e81a9`. -/
noncomputable def hatLM (q : { q : ℂ // ‖q‖ < 1 }) (m : { m : ℕ // 1 ≤ m }) : ℂ :=
  tsum (hatLMSummand q m)

/-- **Terms of the Lambert-type series $L_m^*$.** For a complex number $q$ with $|q| < 1$, an
integer $m \ge 1$ and a natural number $k$, the term of index $k$ is
$q^{(2k+1)m} / (1 - q^{2k+1})^{2m}$, that is, $q^{(2n-1)m} / (1 - q^{2n-1})^{2m}$ with $n = k + 1$.

Source: Gerhold, concept `jis_sem_e9cabece6d32bf6b52d62673`,
source `jis_f69070cf1636bd79774e81a9`. -/
noncomputable def starLMSummand (q : { q : ℂ // ‖q‖ < 1 }) (m : { m : ℕ // 1 ≤ m }) (k : ℕ) : ℂ :=
  (q.val ^ ((2 * k + 1) * m.val)) / ((1 - q.val ^ (2 * k + 1)) ^ (2 * m.val))

/-- **Summability of the Lambert-type series $L_m^*$.** For a complex number $q$ with $|q| < 1$
and an integer $m \ge 1$, this predicate holds when the series
$\sum_{n \ge 1} q^{(2n-1)m} / (1 - q^{2n-1})^{2m}$ is summable in $\mathbb{C}$.

Source: Gerhold, concept `jis_sem_e9cabece6d32bf6b52d62673`,
source `jis_f69070cf1636bd79774e81a9`. -/
noncomputable def starLMSummable (q : { q : ℂ // ‖q‖ < 1 }) (m : { m : ℕ // 1 ≤ m }) : Prop :=
  Summable (starLMSummand q m)

/-- **The Lambert-type series $L_m^*$.** For a complex number $q$ with $|q| < 1$ and an integer
$m \ge 1$, $L_m^*(q) = \sum_{n \ge 1} q^{(2n-1)m} / (1 - q^{2n-1})^{2m}$, where the sum is taken
to be $0$ if the series is not summable.

Source: Gerhold, concept `jis_sem_e9cabece6d32bf6b52d62673`,
source `jis_f69070cf1636bd79774e81a9`. -/
noncomputable def starLM (q : { q : ℂ // ‖q‖ < 1 }) (m : { m : ℕ // 1 ≤ m }) : ℂ :=
  tsum (starLMSummand q m)

end

end MetaMathlibExt
