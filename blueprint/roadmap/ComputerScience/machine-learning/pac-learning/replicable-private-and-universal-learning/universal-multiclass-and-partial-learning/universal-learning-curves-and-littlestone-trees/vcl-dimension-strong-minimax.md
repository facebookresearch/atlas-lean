# The VCL dimension characterizes strong minimax lower bounds

Let $H$ have VC dimension $d < \infty$ and VCL dimension $d_{\mathrm{VCL}}$. Say that $d'/n$ is a **strong minimax lower bound** for $H$ if for every learner there are a single realizable $P$ and $c > 0$ such that $\mathbb{E}[\mathrm{er}_P(\hat h_n)] \ge c\, d'/n$ for infinitely many $n$. Then $d'/n$ is a strong minimax lower bound (up to absolute constants) if and only if $d' \lesssim d_{\mathrm{VCL}}$. Moreover, for classes with finite VCL dimension the optimal learning curve decomposes as a linear term $d_{\mathrm{VCL}}/n$, determined by the class alone, plus an exponentially decaying term whose constants depend on the target distribution. In particular halfspaces in $\mathbb{R}^d$ satisfy a strong minimax lower bound of order $d/n$, recovering the Antos–Lugosi lower bound.

## Proof sketch

The lower bound embeds the random-branch construction of the linear lower bound into an infinite tree whose nodes carry shattered tuples of length $d_{\mathrm{VCL}}$, giving error of order $d_{\mathrm{VCL}}/n$ along a subsequence for a fixed distribution. The upper bound runs a Gale–Stewart game whose learner, after finitely many data-dependent steps, reduces the target to a class with VC dimension at most $d_{\mathrm{VCL}}$ on the relevant region; the finitely many steps contribute the exponential term and the reduced class contributes $O(d_{\mathrm{VCL}}/n)$.

## Depends on

- [Realizable distributions, learning curves and universal rates](universal-rate.md)
- [VCL trees and the VCL dimension](vcl-tree.md)

## Proof depends on

- [Classes with no infinite VCL tree are learnable at linear rate](linear-rate-upper-bound.md)
- [An infinite Littlestone tree forbids rates faster than linear](infinite-littlestone-tree-linear-lower-bound.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, J. Shafer, I. Tolstikhin, "Fine-Grained Distribution-Dependent Learning Curves", COLT (2023), arXiv:2208.14615.
