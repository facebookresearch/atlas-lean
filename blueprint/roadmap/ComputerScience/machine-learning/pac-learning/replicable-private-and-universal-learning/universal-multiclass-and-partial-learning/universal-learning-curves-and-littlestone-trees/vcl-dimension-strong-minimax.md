# The VCL dimension characterizes strong minimax lower bounds

Let $H \subseteq \{0,1\}^X$ satisfy the measurability assumptions of Bousquet, Hanneke, Moran, van Handel and Yehudayoff, with VC dimension $d < \infty$ and VCL dimension $d_{\mathrm{VCL}} \le d$. Say that $d'/n$ is a **strong minimax lower bound** for $H$ if for every learner there is a single realizable $P$ such that $\mathbb{E}[\mathrm{er}_P(\hat h_n)] \ge d'/n$ for infinitely many $n$. Then there are universal constants $\alpha, \beta > 0$ such that the largest $d'$ for which $d'/n$ is a strong minimax lower bound satisfies $\alpha\, d_{\mathrm{VCL}} \le d' \le \beta\, d_{\mathrm{VCL}}$. More generally, for every class with $d_{\mathrm{VCL}} < \infty$ (finite VC dimension not assumed) the optimal expected error satisfies $\Omega(d_{\mathrm{VCL}})/n \le \mathrm{Opt} \le O(d_{\mathrm{VCL}})/n + C e^{-cn}$, where the lower bound holds, for every learner, for one distribution and infinitely many $n$, the upper bound holds for one learner, every realizable distribution and all $n$, $C, c$ depend on the class and the distribution, and the $\Omega, O$ constants are universal. In particular halfspaces in $\mathbb{R}^d$ satisfy a strong minimax lower bound of order $d/n$, recovering the Antos–Lugosi lower bound.

## Proof sketch

The lower bound embeds the random-branch construction of the linear lower bound into an infinite tree whose nodes carry shattered tuples of length $d_{\mathrm{VCL}}$, giving error of order $d_{\mathrm{VCL}}/n$ along a subsequence for a fixed distribution. The upper bound runs a Gale–Stewart game whose learner, after finitely many data-dependent steps, reduces the target to a class with VC dimension at most $d_{\mathrm{VCL}}$ on the relevant region; the finitely many steps contribute the exponential term and the reduced class contributes $O(d_{\mathrm{VCL}}/n)$.

## Depends on

- [Realizable distributions, learning curves and universal rates](universal-rate.md)
- [VCL trees and the VCL dimension](vcl-tree.md)

## Proof depends on

- [Classes with no infinite VCL tree are learnable at linear rate](linear-rate-upper-bound.md)
- [An infinite Littlestone tree forbids rates faster than linear](infinite-littlestone-tree-linear-lower-bound.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, J. Shafer, I. Tolstikhin, "Fine-Grained Distribution-Dependent Learning Curves", COLT (2023), arXiv:2208.14615, Section 1.1 (items 1, 2 and 6), Definitions 2.14–2.16, Theorems 3.1 and 3.3.
