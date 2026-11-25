# Gale transform

Let $v_1, \dots, v_n$ be points in a real vector space and let $b_1, \dots, b_r$ be a basis of
their space of affine dependences. The Gale transform sends the index $i$ to

$$g_i = (b_1(i), \dots, b_r(i)) \in \mathbb{R}^r,$$

the $i$-th row of the $n \times r$ matrix whose columns are the basis vectors. For a configuration
affinely spanning a $d$-dimensional space, $r = n - d - 1$. The transform depends on the chosen
basis only up to a linear change of coordinates in $\mathbb{R}^r$. The basic duality says that, for a proper subset $S$, $\{v_i : i \in S\}$ spans a face of $\operatorname{conv}\{v_1, \dots, v_n\}$
containing no other $v_j$ exactly when $0$ lies in the relative interior of
$\operatorname{conv}\{g_j : j \notin S\}$.

## Sources

- G. M. Ziegler (joint work with R. Sanyal and T. Schröder), "Projected polytopes, Gale diagrams, and polyhedral surfaces", Oberwolfach workshop report, https://www.mi.fu-berlin.de/math/groups/discgeom/ziegler/Preprintfiles/102a-PREPRINT.pdf.
