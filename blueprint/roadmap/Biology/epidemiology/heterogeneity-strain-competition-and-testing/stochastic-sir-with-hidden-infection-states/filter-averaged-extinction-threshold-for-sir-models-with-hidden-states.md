# Filter-averaged extinction threshold for SIR models with hidden states

**Model.** Let $\alpha(t)\in[0,1]$ be the (unobserved) fraction of hidden-state individuals that are infected, a Markov-Feller signal with unique invariant measure $\mu^*$ and $\int|P_tl-\mu^*(l)|\,d\mu\to0$. It is observed only through $dy(t)=g(\alpha(t))\,dt+dW(t)$, and $\Pi_t(\cdot)=\mathbb{P}[\alpha(t)\in\cdot\mid\mathcal{F}^y_t]$ is the nonlinear (Fujisaki-Kallianpur-Kunita) filter. With independent Brownian motions $B_1,B_2$,

$$\begin{aligned}
dS&=\Big[a_1-b_1S-I\!\int_0^1\! f(x,S,I)\,\Pi_t(dx)-I\!\int_0^1\! x\,h(x,S,I)\,\Pi_t(dx)\Big]dt+\sigma_1S\,dB_1,\\
dI&=\Big[-b_2I+I\!\int_0^1\! f(x,S,I)\,\Pi_t(dx)+I\!\int_0^1\! x\,h(x,S,I)\,\Pi_t(dx)\Big]dt+\sigma_2I\,dB_2,
\end{aligned}$$

where $f,h\ge0$ are Lipschitz incidence functions covering bilinear, Beddington-DeAngelis and Holling II forms ($h$ is the extra transmission by hidden infecteds). Let $\hat\mu$ be the stationary law of the disease-free equation $d\varphi=(a_1-b_1\varphi)dt+\sigma_1\varphi\,dB_1$ and $c_2=b_2+\sigma_2^2/2$.

**Threshold.**

$$\lambda:=-c_2+\int_0^\infty\!\!\int_0^1 f(x,y,0)\,\mu^*(dx)\,\hat\mu(dy)+\int_0^\infty\!\!\int_0^1 x\,h(x,y,0)\,\mu^*(dx)\,\hat\mu(dy).$$

**Statements.**
1. The filter $(\Pi_t)$ is a Markov-Feller process on probability measures on $[0,1]$ with a unique invariant measure $\Phi^*$ whose barycenter is $\mu^*$; $(S,I,\Pi)$ is a strong Markov Feller process with $S,I>0$ for all time when $I(0)>0$.
2. *(Extinction.)* If $\lambda<0$, then for all positive initial data $\limsup_{t\to\infty}\frac{\ln I(t)}{t}=\lambda$ almost surely, and $S(t)$ converges weakly to the disease-free process $\varphi$.
3. *(Permanence.)* If $\lambda>0$, the system is permanent in mean.
4. *(Same threshold.)* When $\alpha$ is a finite-state hidden Markov chain (Wonham filter), the same statements hold, and the observed (filtered) system and the original system with $\alpha$ in place of $\Pi_t$ share the threshold $\lambda$. A naive threshold computed by plugging a predicted constant fraction into the rates can be either over- or under-cautious, depending on explicit inequalities between the averages of $f$ and $h$ over $\mu^*$ and $\hat\mu$.

## Expansion

By Itô's formula, $\frac{\ln I(t)}{t}=\frac{\ln I(0)}{t}+\frac{\sigma_2B_2(t)}{t}-c_2+\frac1t\int_0^t\!\!\int(f+xh)(x,S_s,I_s)\,\Pi_s(dx)\,ds$. Near the disease-free boundary $S\approx\varphi$ and $I\approx0$, and the time average of the integrand converges by ergodicity of $(\varphi,\Pi)$ to the same expression with $\Phi^*$; since $\mu^*$ is the barycenter of $\Phi^*$ and the integrand is linear in the filter, $\Phi^*$ may be replaced by $\mu^*$, giving $\lambda$ as the invasion rate of the infection. Negative invasion rate yields exponential extinction; positive invasion rate excludes invariant measures on the boundary and gives permanence. The filter only enters linearly, which is why observing $\alpha$ through noise does not move the threshold.

## Sources

- Nguyen Du, Alexandru Hening, Nhu Nguyen and George Yin, "Hybrid stochastic epidemic SIR models with hidden states", Nonlinear Analysis: Hybrid Systems 49 (2023), 101368, <https://doi.org/10.1016/j.nahs.2023.101368>; numbering as in arXiv:2201.06708: Section 2 (Propositions 2.1-2.2 and threshold (eq-lambda)), Theorems 3.1-3.6, Propositions 4.1-4.3.
