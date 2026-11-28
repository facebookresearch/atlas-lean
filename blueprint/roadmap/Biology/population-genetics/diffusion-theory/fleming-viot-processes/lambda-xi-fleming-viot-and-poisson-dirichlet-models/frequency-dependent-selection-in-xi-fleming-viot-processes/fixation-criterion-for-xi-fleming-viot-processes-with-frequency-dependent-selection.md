# Fixation criterion for the Ξ-Fleming-Viot process with frequency-dependent selection

**Model.** Let $\nabla_\infty=\{z=(z_1,z_2,\dots): z_1\ge z_2\ge\dots\ge0,\ \sum_i z_i\le1\}$ and let $\Xi$ be a probability measure on $\nabla_\infty$ with no atom at $0$ (it governs simultaneous multiple reproduction events). Let $\pi=(\pi_k)_{k\ge1}$ be a probability distribution on $\mathbb{N}\cup\{\infty\}$ with mean $\beta=\sum_k k\pi_k<\infty$, let $K^*\sim\pi$, and set $s(x)=\sum_{k\ge1}\mathbb{P}(K^*\ge k)\,x^{k-1}$. The two-type $\Xi$-Fleming-Viot process with frequency-dependent selection of strength $\kappa>0$ is the $[0,1]$-valued process $X_t$ (frequency of the disfavoured type $0$) with generator

$$Af(x) = -\kappa\, s(x)\,x(1-x)\,f'(x) + \int_{\nabla_\infty}\mathbb{E}\Bigl[f\bigl(x(1-|z|)+\textstyle\sum_i z_iB_i\bigr)-f(x)\Bigr]\frac{\Xi(dz)}{\sum_i z_i^2},$$

where $|z|=\sum_i z_i$ and $B_1,B_2,\dots$ are i.i.d. Bernoulli$(x)$. It arises as the scaling limit of Cannings-type "Wright-Fisher graph" models in which each offspring picks a random number $K$ of potential parents and inherits the type of the fittest one; $\pi$ is the limiting law of $K-1$ given $K>1$.

**Duality.** $X$ is moment dual to the branching-coalescing block-counting process $(D_t)$ on $\mathbb{N}\cup\{\infty\}$ that jumps $n\to n+i$ at rate $n\kappa\pi_i$ for $i\in\mathbb{N}\cup\{\infty\}$ (branching, from selection: each block independently splits at rate $\kappa$ into $1+K^*$ blocks) and merges blocks according to $\Xi$ (each block joins a paintbox event with probability $|z|$, groups by the multinomial weights $z$):

$$\mathbb{E}_x\bigl[X_t^n\bigr]=\mathbb{E}_n\bigl[x^{D_t}\bigr], \qquad x\in[0,1],\ n\in\mathbb{N},\ t\ge0.$$

These rates follow from $(1-x)s(x)=1-\sum_i\pi_ix^i$, so that the selection drift acts on $x^n$ as $-\kappa s(x)x(1-x)\,nx^{n-1}=n\kappa\sum_i\pi_i\,(x^{n+i}-x^n)$, and they agree with Cordero, Hummel and Schertzer (arXiv:1903.06731, Definition 2.12, where each of the $n$ lines branches at its own rate, Corollary 2.15(2) and Remark 2.16).

**Correction to the source's dual rates.** The source states the duality in its Proposition 3.8 for the branching-coalescing process of its Definition 3.7, whose generator, display (35), prints the selection part as

$$a\sum_{i=0}^\infty p_i\big[f(n+i-1)-f(n)\big]\quad\text{with } a=\kappa,\ p=\pi,$$

that is, a jump $n\to n+i-1$ at rate $\kappa\pi_i$, not depending on $n$. The proof of Proposition 3.8 then prints, in display (37),

$$Ax^n=\kappa\sum_{i=1}^\infty\pi_i\big[x^{n+i}-x^n\big]+\sigma\binom n2\big(x^{n-1}-x^n\big).$$

Both displays drop the factor $n$, and (35) is in addition offset by one. Neither matches the source's own generator, display (24) in its Remark 3.5, whose selection term $\kappa\sum_{i\ge1}\pi_i(x^{i+1}-x)f'(x)$ equals $-\kappa s(x)x(1-x)f'(x)$ (the computation in the source's Remark 3.5) and so acts on $x^n$ as $n\kappa\sum_i\pi_i(x^{n+i}-x^n)$. With the rates of (35) the duality already fails at $n=1$, where they give $\kappa\sum_i\pi_i(x^i-x)$ in place of $\kappa\sum_i\pi_i(x^{i+1}-x)$; (37) is correct at $n=1$ but off by the factor $n$ for $n\ge2$ (for $\Xi=0$, $\sigma=0$, $\pi=\delta_1$: $Ax^2=2\kappa(x^3-x^2)$, while (37) gives $\kappa(x^3-x^2)$). This page therefore uses the rate $n\kappa\pi_i$ for $n\to n+i$ computed above.

**Theorem (fixation threshold).** Suppose $\Xi$ is *admissible*: for $\Xi$-a.e. $z$ there are $c_n$ with $nc_n\to0$ and $m(z,c_n)/\sqrt n\to0$, where $m(z,c)=\inf\{k:\sum_{i\le k}z_i>|z|(1-c)\}$ (every $\Xi$ supported on finitely many coordinates, hence every $\Lambda$-coalescent measure, and every stick-breaking law such as Poisson-Dirichlet is admissible). Let $Z\sim\Xi$, $Z^*_i=Z_i/|Z|$, $S$ with density $2v\,dv$ on $[0,1]$ (that is, $\mathbb P(S\le v)=v^2$), independent of $Z$, $W=|Z|S$, and

$$\kappa^* = \frac{1}{2\beta}\,\mathbb{E}\Bigl[\frac{1}{\sum_i (Z^*_i)^2}\cdot\frac{1}{W(1-W)}\Bigr].$$

If $\kappa^*<\infty$, then $D$ has a unique stationary distribution $\mu$ if and only if $\kappa<\kappa^*$. Consequently $\mathbb{P}_x(\lim_t X_t=0)=1$ for all $x\in[0,1)$ if and only if $\kappa\ge\kappa^*$; when $\kappa<\kappa^*$, $X_t$ is absorbed at $0$ or $1$ with $\mathbb{P}_x(\lim_t X_t=0)=1-\varphi_\mu(x)$, where $\varphi_\mu$ is the generating function of $\mu$. (The state $1$ is absorbing, so $x=1$ is excluded. The source's Lemma 4.7(ii) prints "If $D_t$ is not positive recurrent then $P_x(\lim_{t\to\infty}X_t=0)=1$ for every $x\in(0,1]$", which is false at $x=1$, where $X_t\equiv1$; its proof bounds $\mathbb{E}_x[\lim_t X_t^n]$ by $x^m$ for every $m$, which forces the limit to vanish only when $x<1$. The proof of Theorem 4.6 applies the lemma with "$p(x)=1$ for all $x\in[0,1)$", the range stated here.)

So selection always wins only above an explicit threshold set by the multiple-merger noise; below it, large reproduction events can fix the disfavoured type.

## Depends on

- [Ξ-coalescents with simultaneous multiple collisions](../../../../../coalescent-theory/coalescents/xi-coalescents-simultaneous-multiple-collisions.md)

## Expansion

1. Moment duality follows from the sampling duality of the prelimiting Wright-Fisher graph: the probability that $n$ sampled individuals are all of type $0$ is propagated backward by the ancestral (potential-parent) process, which branches when an individual has several potential parents and coalesces when parents are shared.
2. Positive recurrence of $D$ gives $\mathbb{E}_x[X_\infty^n]=\varphi_\mu(x)$ for all $n$, forcing $X_\infty\in\{0,1\}$ with the stated law; transience or null recurrence gives $\mathbb{E}_x[X_\infty^n]=0$.
3. A Griffiths-type representation of the generator as a drift plus an averaged second-order term with random weights $Z^*$, $W$ compares branching drift $\kappa\beta n$ with coalescence drift of order $n/\kappa^*$ at large $n$; admissibility controls how many families a large paintbox splits into, giving the sharp threshold.

## Sources

- Adrián González Casanova and Dario Spanò, "Duality and fixation in $\Xi$-Wright–Fisher processes with frequency-dependent selection", *Ann. Appl. Probab.* 28(1) (2018), 250–284. <https://doi.org/10.1214/17-AAP1305>
- Preprint version (the locators in this item follow its numbering): A. González Casanova, D. Spanò, *Duality and fixation in Ξ-Wright-Fisher processes with frequency-dependent selection*, arXiv:1612.04947 (Proposition 2.9, Propositions 3.4 and 3.8, Remark 3.5, Definition 3.7 and displays (24), (35) and (37), Lemmas 4.1 and 4.7, Definition 4.3 and Theorem 4.6). <https://doi.org/10.48550/arXiv.1612.04947>
