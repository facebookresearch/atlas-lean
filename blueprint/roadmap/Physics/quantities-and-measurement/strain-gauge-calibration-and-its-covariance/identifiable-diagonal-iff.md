# Strains are identifiable from gain-scaled readings iff no gain is zero

For real gains $g = (g_1, \dots, g_n)$, consider the linear map
$\varepsilon \mapsto \operatorname{diag}(g)\,\varepsilon$ on strain vectors, the forward calibration
without offset. It is
[identifiable](../covariance-propagation-and-lipschitz-error-bound/identifiable.md), that is,
injective, if and only if no gain is zero:

$$
\bigl(\operatorname{diag}(g)\,\varepsilon = \operatorname{diag}(g)\,\varepsilon'
\Rightarrow \varepsilon = \varepsilon' \text{ for all } \varepsilon, \varepsilon'\bigr)
\iff g_i \ne 0 \text{ for every } i.
$$

If some $g_i = 0$, two strain vectors that differ only in component $i$ have the same image.
Identifiability here is the linear-algebraic notion, injectivity of the forward map; it is not
statistical identifiability, and the gains are given, not estimated.
