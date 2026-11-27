# Recurrence and transience of the two-type replicator–mutator dynamic with a Markov-switched mutation rate

**Model.** Two types with coordination payoffs $b_{11}=b_{22}=1$, $b_1:=b_{12}\in[0,1)$, $b_2:=b_{21}\in[0,1)$, and type-1 frequency $x\in[0,1]$. For a mutation (behavior-switching) rate $\mu\in[0,1]$ the replicator–mutator dynamic is

$$\dot x = Y_\mu(x) := x\,[b_1+x(1-b_1)]\,(1-\mu-x) + (1-x)\,[1+x(b_2-1)]\,(\mu-x).$$

It has a critical value $\mu_c$: for $\mu<\mu_c$ there are three fixed points $a_1<a_2<a_3$ ($a_1,a_3$ stable, $a_2$ unstable); for $\mu>\mu_c$ there is a single globally stable fixed point $\hat a$, with $a_1<\hat a<a_2$ when $b_2>b_1$ and $a_2<\hat a<a_3$ when $b_2<b_1$. When $b_1=b_2$ the bifurcation is a pitchfork, $\hat a=a_2$ and $\mu_c=(1-b_1)/4$.

Fix $\mu_1<\mu_c<\mu_2$ and let $r(t)\in\{1,2\}$ be an independent continuous-time Markov chain with generator $Q=\begin{pmatrix}-q_{12}&q_{12}\\ q_{21}&-q_{21}\end{pmatrix}$, $q_{12},q_{21}>0$. The switched dynamic is the piecewise-deterministic Markov process $Y(t)=(x(t),r(t))$ with $\dot x(t)=Y_{\mu_{r(t)}}(x(t))$; its generator acts on $V(x,i)$, $C^2$ in $x$, by $LV(x,i)=V'(x,i)\,Y_{\mu_i}(x)+q_{ij}\,[V(x,j)-V(x,i)]$, $j\neq i$.

**Statement.** Below, $a_1,a_2,a_3$ are the fixed points for $\mu_1$ and $\hat a$ is the fixed point for $\mu_2$.

1. *(Boundary repulsion.)* From $x_0\in(0,a_1)$ (resp. $(a_3,1)$) the hitting time of $a_1$ (resp. $a_3$) has finite expectation, and $a_1,a_3$ are stochastically unstable from inside; hence $x(t)$ stays in $(0,1)$ almost surely and all moments of $x(t)$ are bounded uniformly in time (the process is tight).
2. *(Invariant recurrent interval.)* If $b_2>b_1$ and $x_0\in(a_1,\hat a)$, then $\mathbb P_{x_0,i}\big(x(t)\in(a_1,\hat a)\ \forall t\big)=1$ and the process is recurrent in $(a_1,\hat a)$. Symmetrically, if $b_2<b_1$ the interval $(\hat a,a_3)$ is invariant and recurrent.
3. *(Transience near the unstable point.)* If $b_2>b_1$, there is $\epsilon>0$ such that started in $(a_2,a_2+\epsilon)$ the process is almost surely transient there; for given $\mu_1,\mu_2$ there exist switching rates $q_{12},q_{21}$ for which the process is transient on all of $(a_2,a_3)$.
4. *(Positive recurrence.)* If $b_2>b_1$ and the switching rates make $(a_2,a_3)$ transient, the process is positive recurrent, eventually living in a subinterval of $(a_1,\hat a)$ from every initial condition. For other rates there can instead be a recurrent subinterval of $(a_2+\hat\epsilon,a_3)$.
5. *(Symmetric payoffs.)* If $b_1=b_2$, then from $x_0\in[0,\hat a)\cup(\hat a,1]$ the process eventually enters $(a_1,\hat a)$ or $(\hat a,a_3)$, according to the initial condition, and is recurrent there.

In the case $b_2>b_1$ (type 1 favored by the payoffs) items 2–4 give the counterintuitive conclusion that for most initial conditions the population settles near $a_1$, i.e. it favors the dominated type 2.

## Expansion

All claims are proved by the stochastic Lyapunov method for switching diffusions/PDMPs. For hitting-time bounds one takes $V(x,i)=-c_i\log(x)$ (or $\log(1-x)$, $\log(a_2-x)$) with $c_1>c_2>0$ close, so that $LV(x,i)\le-\kappa<0$ on the relevant interval; Dynkin's formula then gives $\mathbb E[\tau\wedge t]\le V(x_0,i)/\kappa$, and monotone convergence finishes. Instability of a fixed point $a$ uses $V(x,i)=(1\mp\alpha c_i)|a-x|^{-\alpha}$, which blows up at $a$ and is a supermartingale nearby because $Y_{\mu_i}(x)/(a-x)$ is bounded for one regime and unbounded with a favorable sign for the other. The switching term $q_{ij}(c_i-c_j)/(1-\alpha c_i)$ controls the size of the transient neighborhood, which is why the generator entries $q_{12},q_{21}$ decide between global transience of $(a_2,a_3)$ and a second recurrent region. Moment bounds use $g(x,i)=x^p$ and $L(e^{\lambda t}g)\le e^{\lambda t}B_p$.

The results correspond to Theorem 3.10 (invariance and recurrence of $(a_1,\hat a)$), Theorem 3.12 and Corollary 3.13 (transience near and on $(a_2,a_3)$), Proposition 3.17 (local recurrence in $(a_2,a_3)$), Theorem 3.19 (positive recurrence) and Theorem 3.21 (the symmetric case) of the source.

## Sources

- A. Vlasic, *Markovian Switching of Mutation Rates in Evolutionary Network Dynamics*, arXiv:2005.00900 (2020). <https://doi.org/10.48550/arXiv.2005.00900>
