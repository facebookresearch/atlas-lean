# Weak zeroth law: lower bound on the variance of relative fitness

**Setting.** Let $(I,\mathcal I)$ and $(I',\mathcal I')$ be measurable spaces carrying finite parent and child population measures $\mu$ and $\mu'$ with sizes $N=\mu(I)>0$ and $N'=\mu'(I')>0$. An evolutionary process $w:\mu\mapsto\mu'$ is a measurable family $i\mapsto w_i$ of finite measures on $I'$ (the children of parent $i$) with $\mu'(B)=\int_I w_i(B)\,\mu(\mathrm di)$ for every $B\in\mathcal I'$. Write $\mathbb E[X]=N^{-1}\int_I X\,\mathrm d\mu$, let $W(i)=w_i(I')$ be the fitness, $\bar W=\mathbb E[W]=N'/N$, and let $U=W/\bar W$ be the relative fitness, so $\mathbb E[U]=1$. Assume $\operatorname{Var}(U)<\infty$ and let
$$p_*=\tfrac1N\,\mu(\{U>0\})\in(0,1]$$
be the proportion of the parent population that leaves at least one child.

**Statement.** The selective change of relative fitness, which by Fisher's identity equals $\operatorname{Var}(U)$, satisfies
$$\operatorname{Var}(U)\;\ge\;\frac1{p_*}-1,$$
with equality if and only if the process is in *selective equilibrium*: $W$ takes only the two values $0$ and $\bar W/p_*$ ($\mu$-a.e.), i.e. every reproducing parent has the same number of children.

**Consequence for environmental change.** If $w':\mu'\mapsto\mu''$ is a second, composable process with relative fitness $U'$ on $I'$, the generalized fundamental theorem $\mathbb E\bigl[(\langle U'\rangle_w-U)\,U\bigr]=-\operatorname{Var}(U)$, where $\langle Y\rangle_w(i)=W(i)^{-1}\int Y\,\mathrm dw_i$, gives
$$\mathbb E\bigl[(\langle U'\rangle_w-U)\,U\bigr]\;\le\;-\Bigl(\frac1{p_*}-1\Bigr),$$
again with equality exactly in selective equilibrium. Death alone (a fraction $1-p_*$ of parents leaving no offspring) therefore forces a minimum amount of selection and an equal and opposite minimum environmental degradation of fitness.

## Depends on

- [Price equation](../natural-selection-fisher-s-theorem-and-the-price/price.md)
- [Variance of fitness](../natural-selection-fisher-s-theorem-and-the-price/fitness-variance.md)

## Expansion

Let $\mathbb E_*[X]=p_*^{-1}\mathbb E[\mathbf 1_{\{U>0\}}X]$ be the average over reproducing parents. Since $U=0$ off $\{U>0\}$,
$$\operatorname{Var}(U)=\mathbb E[(U-1)^2]=(1-p_*)+p_*\,\mathbb E_*[(U-1)^2].$$
Jensen's inequality for the convex map $x\mapsto(x-1)^2$ and $\mathbb E_*[U]=1/p_*$ give $\mathbb E_*[(U-1)^2]\ge(1/p_*-1)^2$, hence $\operatorname{Var}(U)\ge(1-p_*)+(1-p_*)(1/p_*-1)=1/p_*-1$. Equality in Jensen holds exactly when $U$ is $\mathbb E_*$-a.s. constant. The environmental bound follows by inserting this into the generalized Fisher theorem, which is the Price equation with $X=U$, $Y=U'$ and $\mathbb E'[U']-\mathbb E[U]=0$.

## Sources

- T. LaGatta, *The Mathematics of Evolution: The Price Equation, Natural Selection, and Environmental Change*, arXiv:2202.10289 (2022): Theorem 2.4 (general Price equation), Theorem 2.8 (generalized Fisher's fundamental theorem), Definition 3.1 (selective equilibrium), Proposition 3.2 (weak zeroth law of natural selection) and Corollary 3.3. <https://doi.org/10.48550/arXiv.2202.10289>
