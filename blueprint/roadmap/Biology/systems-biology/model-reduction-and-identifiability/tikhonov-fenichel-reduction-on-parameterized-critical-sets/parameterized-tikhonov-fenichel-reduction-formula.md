# Parameterized Tikhonov–Fenichel reduction formula

**Setting.** Let $U\subseteq\mathbb{R}^n$ be open and consider a smooth $\varepsilon$-dependent system

$$
\dot x=h^{(0)}(x)+\varepsilon h^{(1)}(x)+O(\varepsilon^2),\qquad x\in U,\ \varepsilon\ge 0,
$$

without any a priori separation into slow and fast variables. Fix $0<r<n$, $s=n-r$, and a point $a$ in the zero set $\mathcal{V}(h^{(0)})$ such that on $Z=\mathcal{V}(h^{(0)})\cap\widetilde U$ (for a neighborhood $\widetilde U$ of $a$): $\operatorname{rank}Dh^{(0)}(x)=r$; $\mathbb{R}^n=\ker Dh^{(0)}(x)\oplus\operatorname{Im}Dh^{(0)}(x)$; and all nonzero eigenvalues of $Dh^{(0)}(x)$ have negative real part. These are exactly the conditions for a local transformation to Tikhonov standard form (Feliu–Kruff–Walcher, Proposition 1, recalling earlier work). Then $h^{(0)}=P\mu$ near $Z$ with $P(x)\in\mathbb{R}^{n\times r}$ of rank $r$, $Z=\mathcal{V}(\mu)\cap\widetilde U$, and the reduced (slow-time) system on the $s$-dimensional critical set $Z$ is

$$
x'=Q(x)h^{(1)}(x),\qquad Q(x)=I_n-P(x)\big(D\mu(x)P(x)\big)^{-1}D\mu(x),
$$

where $Q(x)$ is the projection onto $\ker Dh^{(0)}(x)$ along $\operatorname{Im}Dh^{(0)}(x)$.

**Theorem (Feliu–Kruff–Walcher, Theorem 1).** Suppose $\Phi:W\to Z$, $W\subseteq\mathbb{R}^s$ open, is a smooth parameterization of the critical set $Z$ with $\operatorname{rank}D\Phi(v)=s$ for all $v\in W$. Then:

1. for every $v\in W$ there is a unique $R(v)\in\mathbb{R}^{s\times n}$ with $Q(\Phi(v))=D\Phi(v)R(v)$;
2. solutions of the reduced system starting in $\Phi(W)$ are $x(t)=\Phi(v(t))$ with

$$
v'=R(v)\,h^{(1)}(\Phi(v));
$$

3. $R(v)$ is characterized by $R(v)P(\Phi(v))=0$ and $R(v)D\Phi(v)=I_s$, i.e. $R(v)\big(D\Phi(v)\,|\,P(\Phi(v))\big)=(I_s\,|\,0)$ with the block matrix invertible, so $R$ is smooth;
4. if $L(x)\in\mathbb{R}^{s\times n}$ has full rank $s$ and $L(x)Dh^{(0)}(x)=0$ on $Z$, then with $L^*(v)=L(\Phi(v))$

$$
v'=\big(L^*(v)D\Phi(v)\big)^{-1}L^*(v)\,h^{(1)}(\Phi(v)).
$$

Thus the reduced equation needs neither $Q$ nor $P$ explicitly, only a parameterization of $Z$ and a basis of the left kernel of $Dh^{(0)}$.

**Graph case (Corollary 1).** If $\Phi(v)=(v,\Phi_2(v))$ and $P=\binom{P_1}{P_2}$ with $P_1\in\mathbb{R}^{s\times r}$, then $R=(R_1\,|\,R_2)$ with $R_2=P_1(D\Phi_2P_1-P_2)^{-1}$ and $R_1=I_s-R_2D\Phi_2$. When moreover $\Phi_2\equiv 0$ (critical set a coordinate subspace) this is the classical quasi-steady-state reduction.

**Conservation laws (Proposition 2).** If $\psi$ is a first integral of the full system for every $\varepsilon$, then $\psi\circ\Phi$ is constant or a first integral of the parameterized reduced system.

## Proof sketch

Differentiating $h^{(0)}(\Phi(v))=0$ gives $Dh^{(0)}(\Phi(v))D\Phi(v)=0$, so the column space of $D\Phi(v)$ is the $s$-dimensional kernel of $Dh^{(0)}$, which is also the image of $Q$. Hence every column of $Q(\Phi(v))$ is a unique combination of the columns of $D\Phi(v)$, giving $R$; substituting $x=\Phi(v)$ into $x'=Qh^{(1)}$ and cancelling the injective $D\Phi(v)$ gives the reduced equation. Since $LP=0$, $R=\Lambda L$ for a unique $s\times s$ matrix $\Lambda$, and $RD\Phi=I_s$ forces $\Lambda=(LD\Phi)^{-1}$.

## Sources

- Elisenda Feliu, Niclas Kruff and Sebastian Walcher, "Tikhonov–Fenichel Reduction for Parameterized Critical Manifolds with Applications to Chemical Reaction Networks", *Journal of Nonlinear Science* 30 (2020), 1355–1380, <https://doi.org/10.1007/s00332-020-09610-3>. Preprint version: arXiv:1905.08306 (2019), <https://doi.org/10.48550/arXiv.1905.08306>.
