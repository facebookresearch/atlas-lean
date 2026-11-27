# Density of the extended mod-minimizer

**Setting.** Fix an alphabet $\Sigma$ of size $\sigma$, a window size $w \ge 1$ and a $k$-mer length $k$. A window is a string of $\ell = w+k-1$ characters, containing $w$ consecutive $k$-mers. A sampling scheme $f:\Sigma^{\ell}\to\{0,\dots,w-1\}$ selects one $k$-mer start in every window; it is a *forward* scheme if, along a string, the absolute selected position never decreases from one window to the next. The *density* of $f$ is the expected fraction of distinct selected $k$-mers on a uniformly random string; every scheme has density at least $1/w$.

**Extended mod-minimizer.** Choose $r \le k$ and set $t = r + ((k-r) \bmod w)$, so that $r \le t \le k$ and $t \equiv k \pmod w$. Let $A:\Sigma^{\ell}\to\{0,\dots,w+k-t-1\}$ be an anchor scheme on $t$-mers, i.e. a sampling scheme for windows of $w+k-t$ consecutive $t$-mers. The extended mod-minimizer selects, in a window whose anchor is the $t$-mer at position $x = A(\text{window})$, the $k$-mer at position $x \bmod w$. The original mod-minimizer is the case where $A$ is the random minimizer (smallest $t$-mer under a uniformly random order); the open-closed mod-minimizer takes $A$ to be the open-closed minimizer, which prefers the smallest open syncmer, then the smallest closed syncmer, then the smallest $t$-mer.

**Theorem 1 (density via the anchor).** If $A$ selects the smallest $t$-mer under a fixed order $\mathcal{O}_t$, then the density of the mod-minimizer equals the probability that, in a context of two consecutive windows (a uniformly random string of $w+k$ characters, containing $w+k-t+1$ $t$-mers), the smallest $t$-mer of the context sits at a position $y$ with $y \equiv 0 \pmod w$.

**Lemma 1 (unique anchors).** For every $\epsilon > 0$, if $t > (3+\epsilon)\log_\sigma(w+k-1)$, the probability that a uniformly random window of $w+k-t$ $t$-mers contains two identical $t$-mers is $o(1/(w+k-1))$.

**Theorem 2 (closed form).** If $t \equiv k \pmod w$ satisfies the hypothesis of Lemma 1 and $A$ is the random minimizer, the density of the extended mod-minimizer is

$$\frac{2 + \frac{k-t}{w}}{w+k-t+1} + o\!\left(\frac{1}{w+k-1}\right).$$

In particular, for fixed $w$ and $k \to \infty$ the density tends to the lower bound $1/w$.

## Expansion

Theorem 1: because $A$ is forward, a new $k$-mer is sampled exactly when the two consecutive windows $W, W'$ select different $k$-mers. Let $y \in \{0,\dots,w+k-t\}$ be the position of the smallest $t$-mer of the two-window context; $w+k-t$ is divisible by $w$ because $t \equiv k \pmod w$. If $y \not\equiv 0 \pmod w$ then $0 < y < w+k-t$, both windows share the anchor, and the selected positions $y \bmod w$ and $((y-1) \bmod w) + 1$ name the same absolute $k$-mer. If $y \equiv 0 \pmod w$ the anchor is the first or last $t$-mer of the context, it lies in only one window, and the sampled $k$-mer changes.

Theorem 2: when the smallest $t$-mer of the context is unique its position is uniform on the $w+k-t+1$ candidates, of which $1 + (w+k-t)/w = 2 + (k-t)/w$ are multiples of $w$; Lemma 1 bounds the contribution of ties by $o(1/(w+k-1))$. Taking $t$ fixed and $k \to \infty$ along $t \equiv k \pmod w$ gives numerator $\approx k/w$ and denominator $\approx k$.

## Sources

- R. Groot Koerkamp, D. Liu, G. E. Pibiri, "The open-closed mod-minimizer algorithm", Algorithms for Molecular Biology 20 (2025) 4, Theorem 1, Lemma 1 and Theorem 2, <https://doi.org/10.1186/s13015-025-00270-0>, PMCID PMC11912762.
