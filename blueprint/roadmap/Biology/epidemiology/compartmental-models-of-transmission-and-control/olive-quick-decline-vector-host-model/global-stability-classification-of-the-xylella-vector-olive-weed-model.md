# Global stability classification of the Xylella vector–olive–weed model

**Model.** Olive Quick Decline Syndrome is caused by *Xylella fastidiosa*, spread by the spittlebug vector *Philaenus spumarius* between olive trees and weeds (a reservoir). In terms of the vector population $F$ with susceptible fraction $U$, olive canopy mass $N$ with susceptible fraction $X$, and weed mass $M$ with susceptible fraction $W$:

$$\begin{aligned}U'&=rM(1-U)-\big[\beta(1-X)+\gamma(1-W)\big]U, & F'&=F\big[r(M-\chi F)-n\big],\\ X'&=X\big[(q+\mu-b\ell)(1-X)-\lambda(1-U)F\big]+\alpha(1-X), & N'&=N\big[qX-\ell-N/C-\mu(1-X)\big],\\ W'&=a(1-W)+W\big[\delta(1-W)-\eta(1-U)F\big], & M'&=M\big[a-M/C_2-\delta(1-W)-h_1\big],\end{aligned}$$

with nonnegative parameters; $\lambda$ and $\eta$ are the transmission rates from infected vectors to olives and to weeds, and $h_1$ is an extra weed-removal rate (weed control). Fractions stay in $(0,1)$ and totals stay bounded, so the box $\bar{\mathcal U}$ is invariant.

**Equilibria.** $E_1$: disease-free, $(U,X,W)=(1,1,1)$, $M=C_2a$, $N=C(q-\ell)$, $F=\chi^{-1}(M-n/r)$. $E_2$: endemic with a nontrivial olive biomass. $E_3$: endemic with olive biomass collapsed, $N=0$. $E_4=(U,0,1,C(q-\ell),W,0)$: vectors and weeds eradicated, olives healthy.

**Theorem.** Assume $a>0$.
1. If $C_2(a-\delta)>n/r$ and $\lambda$ is small enough that the olive susceptible fraction at $E_2$ satisfies $X_2\in\big(\tfrac{\mu+\ell}{\mu+q},1\big)$, then $E_2$ is globally asymptotically stable in $\mathcal{U}$ (resistant cultivars coexist with the infection).
2. If $h_1=0$, $C_2(a-\delta)>n/r$ and $\lambda$ is large enough that $X_2<\tfrac{\mu+\ell}{\mu+q}$, then $E_3$ is globally asymptotically stable in $\mathcal{U}\cup\{N=0\}$ (susceptible cultivars are lost).
3. If $C_2a>n/r$ and $\lambda=\eta=0$, the disease-free $E_1$ is globally asymptotically stable.
4. If $h_1>a$, i.e. weeds are removed faster than they regrow, then $E_4$ is globally asymptotically stable in $\bar{\mathcal U}\setminus\{N=0\}$: removing the weed reservoir eliminates the vector and saves the olive trees without removing them.

## Expansion

The weed equation gives $M'\le M(a-h_1-M/C_2)$, so $h_1>a$ drives $M\to0$; vectors then starve because their growth $r(M-\chi F)-n$ becomes negative, and with no infected vectors the olive fraction returns to $X=1$. In the endemic regimes, the threshold $X=(\mu+\ell)/(\mu+q)$ is exactly where the per-mass olive growth $qX-\ell-\mu(1-X)$ changes sign, separating survival of the olive stand from its collapse. Global stability of $E_2$ is proved with a Lyapunov function in the centered variables.

## Sources

- Edoardo Beretta, Vincenzo Capasso, Simone Scacchi, Matteo Brunetti and Matteo Montagna, "Qualitative analysis of a mathematical model for Xylella fastidiosa epidemics", arXiv:2106.08120 (2021), system in Section 3, equilibria of Section 4 and Theorems 1–4 of Section 5, <https://doi.org/10.48550/arXiv.2106.08120>.
