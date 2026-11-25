# Center Descent

Descent of the boundary trace to $W$. Let $V$ and $W$ be normal varieties over $k$ in
characteristic $p$, with $p$ prime and with local rings at points of codimension one that are
discrete valuation rings; let $F^e$ be the $e$-th iterate of absolute Frobenius, with derived direct
image along $F^e$ (for the derived direct images given by `HasDerivedPushforwards`) having a right
adjoint on $V$ and on $W$; and let $i : W \to V$ be a $k$-morphism with
$F^e_V \circ i = i \circ F^e_W$. Let $\mathcal{M}$ be the divisorial sheaf
$\mathcal{O}_V(\lfloor (1 - p^e)(K_V + D) \rfloor)$ (`sourceModule`), for the chosen canonical
divisor $K_V$ (`C`) and the boundary $D$, and $F^e_{V*}\mathcal{M} \to \mathcal{O}_V$ the boundary
trace (`boundaryTrace`, for the chosen Frobenius identification `F` and index `I`). The data is a
map $\phi : F^e_{W*}\, i^*\mathcal{M} \to \mathcal{O}_W$ such that the base-change map
$i^* F^e_{V*}\mathcal{M} \to F^e_{W*}\, i^*\mathcal{M}$ is an epimorphism and its composite with
$\phi$ is $i^*$ of the boundary trace followed by $i^*\mathcal{O}_V \cong \mathcal{O}_W$.
