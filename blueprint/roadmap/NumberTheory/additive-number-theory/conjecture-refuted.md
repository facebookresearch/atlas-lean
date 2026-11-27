# Disproof of Erdős Problem 1 on distinct subset sums

There is no real number $C > 0$
such that for every natural number $N \ne 0$ and every finite set $A \subseteq \{1, \dots, N\}$
whose distinct subsets have distinct sums, $C \cdot 2^{|A|} < N$.

Equivalently, Erdős's conjecture $N \gg 2^{|A|}$ for sum-distinct sets $A \subseteq \{1, \dots, N\}$
is false: for every $\varepsilon > 0$ there are arbitrarily large $n$ and sum-distinct sets
$A \subseteq \{1, \dots, N\}$ with $|A| = n$ and $N \le \varepsilon \, 2^n$. The disproof was found
by GPT-6 Astra in the FrontierMath Erdős benchmark, with a machine-checked proof.

## Sources

- T. F. Bloom, Erdős Problem #1, https://www.erdosproblems.com/1 (disproof by GPT-6 Astra; see the proof exposition there).
- Tom Adamczewski, *Erdős problem #1: disproof*, machine-checked disproof written by GPT-6 Astra in the FrontierMath Erdős benchmark (Adamczewski and Bloom, 2026), https://github.com/tadamcz/erdos1/blob/0e395153306f34b3829d118b85bdd704136f2843/Erdos1/Resolutions/Erdos1_219usd_38h.lean#L2419 (commit 0e395153306f34b3829d118b85bdd704136f2843, theorem `Erdos1.erdos_1.disproof`).
