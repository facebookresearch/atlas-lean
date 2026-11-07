# Principle of local reflexivity

Let $E$ be a Banach space over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$, with dual $E^*$, bidual $E^{**}$ and canonical embedding $J \colon E \to E^{**}$.
Let $M$ and $N$ be finite-dimensional normed spaces over $\mathbb{K}$ with injective bounded
linear maps $i_M \colon M \to E^{**}$ and $i_N \colon N \to E^*$, and let $\varepsilon > 0$. Then
there is a bounded linear map $T \colon M \to E$ such that for all $m \in M$, $n \in N$ and
$x \in E$ we have
$(1 + \varepsilon)^{-1} \|i_M(m)\| \le \|T m\| \le (1 + \varepsilon) \|i_M(m)\|$,
$i_N(n)(T m) = i_M(m)(i_N(n))$, and $T m = x$ whenever $i_M(m) = J x$.

Proof: Helly's lemma applied to finitely many linear conditions plus one norm bound, then a finite
$\delta$-net of the unit sphere of $i_M(M)$ turns net-point bounds into the $(1+\varepsilon)$
bounds (the elementary proof in Albiac–Kalton, *Topics in Banach Space Theory*).

## Sources

- J. Lindenstrauss and H. Rosenthal, Israel J. Math. 7 (1969) 325-349, principle of local reflexivity; Johnson-Rosenthal-Zippin 1971 refinements; Albiac and Kalton, Topics in Banach Space Theory; Lean states `RCLike` Banach finite- dimensional `M, N` version with `(1+ε)`-isometry and pairing preservation.
