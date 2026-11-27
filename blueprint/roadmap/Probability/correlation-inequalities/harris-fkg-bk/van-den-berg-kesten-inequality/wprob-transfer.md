# Weighted probability is invariant under relabeling coordinates

Let $E$ and $F$ be finite sets, $e : E \to F$ a bijection, $\varphi : E \times \{0,1\} \to \mathbb{R}$ and $S \subseteq \{0,1\}^E$. Then

$$P_\varphi(S) = P_{\varphi'}(\{\omega \in \{0,1\}^F : \omega \circ e \in S\}), \qquad \varphi'_y = \varphi_{e^{-1}(y)},$$

where $P$ is the [weighted probability](wprob.md).
