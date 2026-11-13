# Berlekamp-Welch key equations

Let $F$ be a field, let $\alpha_0, \dots, \alpha_{n-1} \in
F$, let $k, e \in \mathbb{N}$ and let $y \in F^n$ be a received word. A pair of polynomials
$(Q, E)$ over $F$ solves the key equations for $y$ when $E$ is monic of degree $e$, $Q$ has degree
less than $e + k$, and $Q(\alpha_i) = y_i E(\alpha_i)$ for every $i < n$.
