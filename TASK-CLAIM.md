# Task claim: binary digit sums in Monroe's Takagi identities

This temporary note opens the draft pull request that claims three ATLAS tasks, Lemmas 14, 15
and 16 of the source; Lemma 16's proof uses Lemma 14, and Lemma 15 is its mirror image. It will
be removed when the proofs land on this branch.

- `af_a311fb51bfced74999f28a61`: `MetaMathlibExt.hammingWeight_succ_of_even` (Lemma 14). If $n$
  is even, then $s_1(n + 1) = s_1(n) + 1$.
- `af_11cf9d82d53ab71265362f3f`: `MetaMathlibExt.hammingWeight_pred_of_odd` (Lemma 15). If $n$ is
  odd, then $s_1(n - 1) = s_1(n) - 1$.
- `af_3324333384fb402c92162d8b`: `MetaMathlibExt.hammingWeight_two_pow_sub_of_odd` (Lemma 16). If
  $r$ is odd and $2r < 2^k$, then $s_1(2^k - r) = 1 + k - s_1(r)$.

Here $s_1(m)$ is the sum of the binary digits of $m$. All three are `theorem_wanted` declarations
in `WantedExt/NumberTheory/TakagiDyadicIdentitiesWanted.lean`, with their pages under
`blueprint/roadmap/Analysis/real-functions/continuity-and-functional-equations/takagi-function/`;
they are to be proved with their names and statements unchanged.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemmas 14, 15 and 16.
