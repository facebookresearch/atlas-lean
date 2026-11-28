# Invariance of counting strategies and time-reversal duality under memory-one adaptive dynamics

**Setting.** In the repeated donation game with benefit $b$ and cost $c$, $b>c>0$ (payoffs $R=b-c$, $S=-c$, $T=b$, $P=0$, so $R+P=S+T$: equal gains from switching), a memory-one strategy is $p=(p_{CC},p_{CD},p_{DC},p_{DD})\in[0,1]^4$, the probability of cooperating after each outcome of the previous round (own move first). For $p,p'\in(0,1)^4$ the pair of strategies induces an ergodic Markov chain on $\{CC,CD,DC,DD\}$ with stationary law $v$, and the repeated-game payoff is $A(p,p')=Rv_{CC}+Sv_{CD}+Tv_{DC}+Pv_{DD}$. *Adaptive dynamics* moves a homogeneous population up the selection gradient,

$$\dot p_{ij}=\frac{\partial A(p,p')}{\partial p_{ij}}\Big|_{p'=p},\qquad i,j\in\{C,D\}.$$

**Theorem.**

(1) *Counting strategies are invariant.* The three-dimensional set $\mathcal C=\{p\in[0,1]^4:p_{CD}=p_{DC}\}$ of strategies that respond only to the number of cooperators in the previous round is invariant: if $p(0)\in\mathcal C$ then $p(t)\in\mathcal C$ for all $t$. Moreover $d=p_{CD}-p_{DC}$ satisfies

$$\dot d=\Phi(p)\,(b-c)\,(1-p_{CD}+p_{DC})\,d\,(p_{CC}-p_{CD}-p_{DC}+p_{DD})$$

for a factor $\Phi(p)$ that is negative in the interior $(0,1)^4$, namely $-p_{DD}(1-p_{DD}+p_{CC})(1-p_{CC})$ divided by the positive common denominator of the dynamics, so $|d|$ decreases exactly where $p_{CC}+p_{DD}>p_{CD}+p_{DC}$; $\mathcal C$ is invariant but not a local attractor. The invariance holds for every symmetric repeated $2\times2$ game; for memory-$n$ strategies and any fixed sequence $s$ of $n-1$ moves, the condition $p_{CsDs}=p_{DsCs}$ is invariant in every repeated $2\times2$ game (Proposition 7).

(2) *Time-reversal duality.* If $p(t)$ solves the dynamics on $(a',b')$, then

$$\tilde p(t)=\big(1-p_{DD},\,1-p_{DC},\,1-p_{CD},\,1-p_{CC}\big)(-t)$$

solves it on $(-b',-a')$. The involution $p\mapsto\tilde p$ is the reflection of $[0,1]^4$ through the plane $\{p_{CC}+p_{DD}=1,\ p_{CD}+p_{DC}=1\}$; it maps critical points to critical points and exchanges forward and backward limit sets. This duality uses equal gains from switching.

## Expansion

Using the determinant representation of the payoff, the adaptive dynamics multiplied by a positive common denominator has the form $\dot p_{ij}\propto f_{ij}\,(b\,g_{ij}+c\,h_{ij})$ with explicit polynomials. One checks $f_{CD}=f_{DC}$ on the relevant arguments, while $g_{CD}-g_{DC}$ and $h_{CD}-h_{DC}$ both factor through $(p_{CD}-p_{DC})(p_{CC}-p_{CD}-p_{DC}+p_{DD})$, giving the equation for $\dot d$ and hence invariance. Conceptually, at a counting strategy the stationary law is unchanged to first order by moving off $\mathcal C$, so no infinitesimal mutant gains by distinguishing $CD$ from $DC$. For the duality, the source gives an intuitive argument through a sequence of payoff-matrix transformations (relabelling cooperation and defection) that is available only when $R+P=S+T$; formally, componentwise one verifies $\dot{\tilde p}_{CC}(-t)=\dot p_{CC}(t)$ from the polynomial forms.

## Depends on

- [Fitness gradient](../../../classification-of-adaptive-dynamics-singular-str/fitness-gradient.md)

## Sources

- LaPorte P, Hilbe C, Nowak MA. Adaptive dynamics of memory-one strategies in the repeated donation game. *PLoS Computational Biology* 19 (2023). <https://doi.org/10.1371/journal.pcbi.1010987> (PMCID: PMC10337984). Eq. (6); Propositions 1, 2, 6 and 7 and Eqs. (17), (18) and (21) in Methods.
