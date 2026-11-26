# Label-forgetfulness characterizes propagation of exchangeability

**Setting.** Let $\mathcal P(\mathbb N)$ be the set of non-empty subsets of $\mathbb N=\{1,2,\dots\}$. A *random ancestry mapping* is a sequence $L=(L(i))_{i\ge 1}$ of $\mathcal P(\mathbb N)$-valued random variables; $L(i)$ is the set of potential parents in generation $0$ of individual $i$ in generation $1$. Extend $L$ to subsets by $L(S)=\bigcup_{i\in S}L(i)$ for $S\subset\mathbb N$.

Given $\{0,1\}$-valued types $(X_0(i))_{i\ge1}$ of generation $0$, independent of $L$, define the types of generation $1$ by

$$X_1(i)=\inf_{j\in L(i)} X_0(j),\qquad i\ge 1,$$

so type $0$ is dominant: individual $i$ has type $1$ only if all of its potential parents have type $1$.

- $L$ **propagates exchangeability** if, for every exchangeable sequence $(X_0(i))_{i\ge1}$ independent of $L$, the sequence $(X_1(i))_{i\ge1}$ is exchangeable.
- $L$ is **label-forgetful** if $|L(S)|\overset{d}{=}|L(S')|$ for all finite $S,S'\subset\mathbb N$ with $|S|=|S'|$.

**Theorem.** A random ancestry mapping $L$ propagates exchangeability if and only if it is label-forgetful.

Examples of label-forgetful mappings include: the branching mapping, in which i.i.d. $\mathbb N$-valued offspring numbers $\xi_1,\xi_2,\dots$ assign to individual $i$ the block of parents $\{j:\sum_{l<i}\xi_l<j\le\sum_{l\le i}\xi_l\}$; a discrete lookdown mapping in which a Bernoulli$(y)$-selected group of individuals all look down to the smallest selected index; and any independent Bernoulli mixture $Y L^1+(1-Y)L^2$ of two label-forgetful mappings. The identity mapping $L(i)=\{i\}$ is label-forgetful although $(L(i))_i$ itself is not exchangeable, so propagation of exchangeability is strictly weaker than exchangeability of the mapping.

## Expansion

*Sufficiency.* Fix indices $n_1,\dots,n_m$ and types $v_1,\dots,v_m\in\{0,1\}$, let $Z=\{j:v_j=1\}$ and $Z^c$ its complement. Writing $\mathbf 1\{X=0\}=1-X$ and expanding by inclusion–exclusion,

$$\mathbb P\big(X_1(n_j)=v_j,\ j\le m\big)=\sum_{G\subset Z^c}(-1)^{|G|}\,\mathbb P\Big(\inf_{i\in L(\{n_j: j\in Z\cup G\})}X_0(i)=1\Big).$$

Because $X_0$ is exchangeable and independent of $L$, each probability depends on the set $L(\cdot)$ only through its cardinality, and by label-forgetfulness that cardinality has the same law as $|L([\,|Z\cup G|\,])|$, where $[k]=\{1,\dots,k\}$. Hence the joint law depends only on $(v_1,\dots,v_m)$, not on the labels $n_j$.

*Necessity.* If $|S|=|S'|$ but $|L(S)|$ and $|L(S')|$ differ in law, take $X_0$ i.i.d. Bernoulli$(x)$; then $\mathbb P(X_1(i)=1\ \forall i\in S)=\mathbb E[x^{|L(S)|}]$ and the analogous quantity for $S'$ differ for some $x$, contradicting exchangeability of $X_1$.

## Sources

- Adrián González Casanova, Ariel Offenstadt and Arno Siri-Jégousse, "Moment duality and propagation of exchangeability", arXiv:2606.28174 (2026), Section 2.1, Theorem 2.1 and Examples 2.2–2.4. <https://doi.org/10.48550/arXiv.2606.28174>
