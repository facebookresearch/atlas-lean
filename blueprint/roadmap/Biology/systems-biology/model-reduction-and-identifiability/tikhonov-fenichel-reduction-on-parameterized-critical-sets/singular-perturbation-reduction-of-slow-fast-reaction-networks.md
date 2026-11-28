# Singular perturbation reduction of slow–fast reaction networks

**Setting.** A mass-action reaction network on species $X_1,\dots,X_n$ is split into fast and slow reactions, giving

$$
\dot x=N_{\mathsf f}\big(K_{\mathsf f}\circ x^{Y_{\mathsf f}}\big)+\varepsilon\,N_{\mathsf s}\big(K_{\mathsf s}\circ x^{Y_{\mathsf s}}\big),
$$

with stoichiometric matrices $N_{\mathsf f},N_{\mathsf s}$, rate-constant vectors $K_{\mathsf f},K_{\mathsf s}>0$, kinetic-order matrices $Y_{\mathsf f},Y_{\mathsf s}$, monomial vectors $x^{Y}=(x^{Y_1},\dots,x^{Y_m})$ and Hadamard product $\circ$. The critical set $Z$ is the set of steady states of the fast subnetwork. **Blanket hypothesis:** the Tikhonov conditions hold on $Z$ (constant rank $r$, kernel–image splitting, nonzero eigenvalues of $Dh^{(0)}$ in the open left half-plane) and $\operatorname{rank}N_{\mathsf f}=\operatorname{rank}Dh^{(0)}(x)=r$ on $Z$. Put $s=n-r$ and let $L_{\mathsf f}\in\mathbb{R}^{s\times n}$ have rows forming a basis of the left kernel of $N_{\mathsf f}$ (the fast conservation laws).

**Proposition (Feliu–Kruff–Walcher, Proposition 3).** For any parameterization $\Phi:W\to Z$ with $\operatorname{rank}D\Phi=s$, the reduced system is

$$
v'=\big(L_{\mathsf f}D\Phi(v)\big)^{-1}L_{\mathsf f}\,N_{\mathsf s}\big(K_{\mathsf s}\circ\Phi(v)^{Y_{\mathsf s}}\big),\qquad v\in W,
$$

and the column space of $P$ in any decomposition $h^{(0)}=P\mu$ equals the column space of $N_{\mathsf f}$. If $\operatorname{rank}N=\operatorname{rank}N_{\mathsf f}$ (slow reactions add no new stoichiometric directions) the reduced system is $v'=0$.

**Complex-balanced fast subnetwork (Proposition 4).** If the fast subnetwork has a positive complex-balanced steady state $x^*$, then $\Phi(v)=x^*\circ v^{L_{\mathsf f}}$, $v\in\mathbb{R}^s_{>0}$, parameterizes the positive critical set, and

$$
v'=\operatorname{diag}(v)\big(L_{\mathsf f}\operatorname{diag}(x^*\circ v^{L_{\mathsf f}})L_{\mathsf f}^{\mathsf T}\big)^{-1}L_{\mathsf f}\,N_{\mathsf s}\big(K_{\mathsf s}\circ (x^*)^{Y_{\mathsf s}}\circ v^{L_{\mathsf f}Y_{\mathsf s}}\big).
$$

**Attractivity (Proposition 5).** If the fast subnetwork is weakly reversible and has deficiency zero, all nonzero eigenvalues of $Dh^{(0)}$ on $Z$ have negative real part, so the attractivity part of the Tikhonov conditions holds automatically.

Rational parameterizations of $Z$ are also available when the fast subnetwork has a non-interacting set of $r$ species with no conservation law supported on it and a path to $0$ from each such species in the induced network: the corresponding $r$ steady-state equations are linear in those species and have a unique positive rational solution in the remaining $s$ concentrations.

## Depends on

- [Parameterized Tikhonov–Fenichel reduction formula](parameterized-tikhonov-fenichel-reduction-formula.md)

## Proof sketch

$L_{\mathsf f}Dh^{(0)}=L_{\mathsf f}N_{\mathsf f}Dw_{\mathsf f}=0$, so $L_{\mathsf f}$ is an admissible left annihilator in the general parameterized formula. For complex-balanced steady states the positive steady-state set is the toric variety $\{x:\ x^{M}=(x^*)^{M}\}$ whose exponent space is the row span of $L_{\mathsf f}$, which gives the monomial parameterization and $D\Phi(v)=\operatorname{diag}(x^*\circ v^{L_{\mathsf f}})L_{\mathsf f}^{\mathsf T}\operatorname{diag}(1/v)$. Attractivity follows from Feinberg's result that in weakly reversible deficiency-zero mass-action systems every positive steady state is linearly attractive within its stoichiometric compatibility class.

## Sources

- Elisenda Feliu, Niclas Kruff and Sebastian Walcher, "Tikhonov–Fenichel Reduction for Parameterized Critical Manifolds with Applications to Chemical Reaction Networks", *Journal of Nonlinear Science* 30 (2020), 1355–1380, <https://doi.org/10.1007/s00332-020-09610-3>. Preprint version: arXiv:1905.08306 (2019), <https://doi.org/10.48550/arXiv.1905.08306>.
