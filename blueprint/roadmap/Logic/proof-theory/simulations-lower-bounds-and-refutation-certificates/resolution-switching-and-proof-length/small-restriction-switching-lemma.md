# Switching lemma for small restrictions

If a random restriction satisfies every $i$-DNF of large covering number with high probability, then after the restriction every $k$-DNF is strongly represented by a short decision tree. The restriction may set only a polynomially small fraction of the variables, which is what makes the lemma usable against Res($k$).

A *term* is a conjunction of literals and a $k$-*DNF* is a disjunction of terms of size at most $k$. A *restriction* $\rho$ maps a set of variables to $\{0,1,\ast\}$, and $F\upharpoonright_{\rho}$ simplifies $F$ only where a subexpression becomes explicitly constant. A *decision tree* is a rooted binary tree whose internal nodes query variables and whose leaves are labeled $0$ or $1$; each root-to-leaf path is a partial assignment, and $\mathrm{Br}_v(T)$ is the set of paths ending in a leaf labeled $v$. A decision tree $T$ *strongly represents* a DNF $F$ if every $\pi\in\mathrm{Br}_0(T)$ falsifies every term of $F$ ($t\upharpoonright_{\pi}=0$ for all $t\in F$) and every $\pi\in\mathrm{Br}_1(T)$ satisfies some term of $F$. The *representation height* $h(F)$ is the minimum height of a decision tree strongly representing $F$. A set $S$ of variables is a *cover* of $F$ if every term of $F$ contains a variable of $S$, and the *covering number* $c(F)$ is the minimum size of a cover.

**Switching lemma.** Let $k\ge 1$, let $s_0,\dots,s_{k-1}$ and $p_1,\dots,p_k$ be positive numbers, and let $\mathcal D$ be a distribution on partial assignments such that for every $i\le k$ and every $i$-DNF $G$ with $c(G)>s_{i-1}$,

$$
\Pr_{\rho\in\mathcal D}\bigl[G\upharpoonright_{\rho}\ne 1\bigr]\le p_i .
$$

Then for every $k$-DNF $F$,

$$
\Pr_{\rho\in\mathcal D}\Bigl[h(F\upharpoonright_{\rho})>\sum_{i=0}^{k-1}s_i\Bigr]\le\sum_{i=1}^{k}2^{\sum_{j=i}^{k-1}s_j}\,p_i .
$$

**Normal form.** Let $k,s,d$ be positive integers and $\gamma,\delta\in(0,1]$, and suppose $\Pr_{\rho\in\mathcal D}[G\upharpoonright_{\rho}\ne 1]\le d\,2^{-\delta c(G)^{\gamma}}$ for every $k$-DNF $G$. Then for every $k$-DNF $F$,

$$
\Pr_{\rho\in\mathcal D}\bigl[h(F\upharpoonright_{\rho})>2s\bigr]\le d\,k\,2^{-\delta' s^{\gamma'}},\qquad \delta'=2(\delta/4)^{k},\quad \gamma'=\gamma^{k}.
$$

**Uniform small restrictions.** Let $\mathcal D_p$ leave each of the $n$ variables unset with probability $1-p$ and set it to $0$ or to $1$ with probability $p/2$ each. For every $k\ge1$ there is $\gamma>0$ such that for every $k$-DNF $F$, every $w>0$ and every $p\ge n^{-1/(2k^2)}$,

$$
\Pr_{\rho\in\mathcal D_p}\bigl[h(F\upharpoonright_{\rho})>w\bigr]\le k\,2^{-\gamma w n^{-1/2}} .
$$

## Expansion

The proof is an induction on $k$ that trades covering number against satisfaction probability. If $c(F)>s_{k-1}$, the hypothesis says $F\upharpoonright_{\rho}=1$ except with probability $p_k$. Otherwise fix a cover $S$ with $|S|\le s_{k-1}$; for every assignment $\pi$ to $S$ the formula $F\upharpoonright_{\pi}$ is a $(k-1)$-DNF, so induction and a union bound over the $2^{|S|}$ choices of $\pi$ give short trees for all of them at once, and querying the unset variables of $S$ first and then running those trees yields a tree of height at most $\sum_{i=0}^{k-1}s_i$ that strongly represents $F\upharpoonright_{\rho}$. The normal form takes $s_i=(\delta/4)^{i}s^{\gamma^{i}}$ and $p_i=d\,2^{-4s_i}$. For $\mathcal D_p$, an $i$-DNF with covering number $c$ has at least $c/i$ variable-disjoint terms, each satisfied independently with probability at least $(p/2)^i$, so $\Pr[G\upharpoonright_{\rho}\ne1]\le e^{-c(G)p^i/(i2^i)}$.

Unlike Håstad-style switching lemmas, the restriction may set as few as $n^{1-\epsilon}$ of the $n$ variables; in exchange, very narrow DNFs become only moderately short trees, so the lemma is applied once rather than iterated. That single application suffices for Res($k$), whose lines are $k$-DNFs. The bridge to resolution width is the companion theorem of the same paper: if a set $\mathcal C$ of clauses of width at most $h$ has a Res($k$) refutation every line $F$ of which has $h(F)\le h$, then $\mathcal C$ has a resolution refutation of width at most $kh$. Hence, if a restriction $\rho$ gives $h(F\upharpoonright_{\rho})\le h$ for every line, then $\mathcal C\upharpoonright_{\rho}$ has a width-$kh$ resolution refutation, and resolution width lower bounds for the restricted formula become Res($k$) size lower bounds. The proof of that companion theorem converts the decision trees into clauses recording falsifying branches and uses strong soundness of Res($k$): any consistent choice of satisfied terms of the premises implies a satisfied term of the conclusion. The same switching lemma also separates depth-$(d+1)$ circuits of bottom fan-in $k$ from those of bottom fan-in $k+1$ exponentially, via modified Sipser functions.

## Depends on

None.

## Proof depends on

None.

## Sources

- Nathan Segerlind, Samuel R. Buss, Russell Impagliazzo, "A Switching Lemma for Small Restrictions and Lower Bounds for k-DNF Resolution", *SIAM Journal on Computing*, 2004, doi:10.1137/S0097539703428555 (Definitions 3.1, 3.2 and 3.5, Theorem 3.3, Corollary 3.4, Lemma 3.6, Corollary 3.7, Lemma 2.2, Theorem 5.1 and Corollary 5.2, Theorem 4.6).
