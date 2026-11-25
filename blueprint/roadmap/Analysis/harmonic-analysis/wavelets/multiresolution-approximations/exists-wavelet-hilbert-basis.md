# Wavelet orthonormal basis of a multiresolution approximation

If $(V_j)$ is a [multiresolution approximation](is-multiresolution-approximation.md) of $L^2(\mathbb{R})$, there is a wavelet $\psi \in L^2(\mathbb{R})$ such that

$$\{\sqrt{2^j}\, \psi(2^j x - k)\}_{(j,k) \in \mathbb{Z}^2}$$

is an orthonormal basis of $L^2(\mathbb{R})$, and for each $j$ the functions of scale $j$ lie in, and form an orthonormal basis of, the orthogonal complement $O_j$ of $V_j$ in $V_{j+1}$ (S. Mallat, *Multiresolution approximations and wavelet orthonormal bases of $L^2(\mathbb{R})$*, Trans. Amer. Math. Soc. 315 (1989), Section 4, the conclusion after (70)). Mallat defines $\psi$ by $\hat\psi(2\omega) = G(\omega)\hat\varphi(\omega)$ with $G(\omega) = e^{-i\omega}\overline{H(\omega + \pi)}$ (equations (63) and (69)), derives the conditions (66) under which the decomposition $V_0 = V_{-1} \oplus O_{-1}$ is orthogonal, and concludes from the density of $\bigoplus_j O_j$ in $L^2(\mathbb{R})$. The statement consists of the basis and the membership $b_{j,k} \in V_{j+1} \cap V_j^\perp$, which together imply the basis property for each $O_j$.
