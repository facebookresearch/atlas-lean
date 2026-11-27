# Stability of a maturity-structured blood cell proliferation model

**Model.** Resting and proliferating cell densities $N(t,m)$, $P(t,m)$ depend on maturity $m\in[0,1]$ ($m=0$: most primitive stem cells). Cells mature at speed $V(m)$, with $V\in C^1$, $V(0)=0$, $V>0$ on $(0,1]$ and $\int_0^m ds/V(s)=\infty$, so immature cells take arbitrarily long to mature. Resting cells die at rate $\delta(m)$ and enter proliferation at rate $\beta(m,N)$; proliferating cells die by apoptosis at rate $\gamma(m)$ and divide into two daughters a maturity-dependent time $\tau(m)$ after entry, with $\tau'(m)+1/V(m)>0$. The resulting system of transport equations with maturity-retarded delays is studied in integrated form.

**Theorems.**

1. **Finite-time forgetting of upper-maturity initial data.** Assume condition (14) ($\Delta(m) < m$ on $(0, 1]$). If two initial data agree on $[0, b]$, then their resting densities agree on $[0, g(1)]$ for all $t \ge \bar{t} = \ln[h(g(1))/h(g(b))] + (N+2)\tau_{\max}$, and both the resting and proliferating densities agree on all of $[0, 1]$ for all $t \ge (N+3)\tau_{\max} - \ln h(g(b))$, where $N$ is the integer given by Lemma 3.1 applied to $g(b)$.

*(2)* *(Stem cell compartment.)* At $m=0$ the resting density $x(t)=N(t,0)$ solves the delay equation

$$x'(t)=-\bigl(\rho+\beta(0,x(t))\bigr)x(t)+2\bar\xi(0)\,\beta(0,x(t-r))\,x(t-r),$$

with $\rho=\delta(0)+V'(0)$ and $r=\tau(0)$. Its solutions are bounded if $\rho>0$, while for $\rho=0$ and $x\beta(0,x)$ eventually decreasing there are unbounded solutions. The trivial solution is globally stable iff $(2\bar\xi(0)-1)\beta(0,0)<\rho$.

*(3)* *(Global stability.)* If $\Delta(m)<m$ on $(0,1]$, where $\Delta(m)$ is the maturity at commitment of a mother cell whose daughters are born with maturity $m$ (daughters are born more mature than their mother was at commitment), and the trivial solution is locally stable, it is globally stable on the set of initial data for which $N(t,0),P(t,0)\to0$. Under the explicit condition

$$\Bigl(1+2\sup\xi\Bigr)\sup_m\beta(m,0)<\min\Bigl\{\inf_m(\delta+V'),\ \inf_m(\gamma+V')\Bigr\},$$

it is globally exponentially stable.

*(4)* *(Instability.)* If $\rho\le(2\bar\xi(0)-1)\beta(0,0)$, the trivial solution is unstable.

So extinction or persistence of the whole blood lineage is decided by the stem cell compartment at $m=0$.

## Depends on

- [Distributed-delay stem cell model and Hopf bifurcation](distributed-delay-stem-cell-model-and-hopf-bifurcation.md)

## Expansion

Along characteristics $\chi(s,m)=h^{-1}(h(m)e^s)$ the transport part is a semigroup on $C[0,1]$ that only moves mass toward higher maturity, so the value at maturity $m$ at time $t$ depends only on data at lower maturities; since every maturity level below $b$ flows past $g(b)$ in finite time, data on $[0,b]$ propagate to the whole interval. At $m=0$ the maturation speed vanishes, the transport term drops out, and the equations reduce to a delay differential equation in which $2\bar\xi(0)$ is the effective number of surviving daughters per division. Comparing loss $\rho+\beta$ with gain $2\bar\xi(0)\beta$ at $x=0$ gives the stability threshold.

## Sources

- M. Adimy, F. Crauste, L. Pujo-Menjouet, "On the stability of a maturity structured model of cellular proliferation", arXiv:0904.2492 (2009), Section 2 (model and integrated formulation, Proposition 2.1), Proposition 3.1, Theorem 3.1, Corollaries 3.1–3.2, Propositions 4.1–4.3, Theorem 4.1, Theorem 5.1, Corollary 5.1 and Theorem 6.1, <https://doi.org/10.48550/arXiv.0904.2492>.
