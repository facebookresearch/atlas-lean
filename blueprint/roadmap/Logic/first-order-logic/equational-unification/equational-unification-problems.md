# Equational unification problems

An $E$-unification problem asks for a substitution that makes the two sides of each of finitely many term equations equal modulo an equational theory $E$; problems are classified as elementary, with constants, or general according to which extra function symbols may occur.

**Equational theories.** For a set $E$ of identities $s \approx t$ between terms over a signature and a countably infinite set of variables, $=_E$ is the least congruence on terms that is closed under substitution and contains $E$ (the relation of the [equational calculus](../equational-logic/equational-calculus.md)). $\mathrm{Sig}(E)$ is the set of function symbols occurring in $E$; a set of identities is also called an equational theory.

**Problems and unifiers.** Let $F \supseteq \mathrm{Sig}(E)$ be a signature. An *$E$-unification problem over $F$* is a finite set

$$
\Gamma = \{s_1 =^?_E t_1, \dots, s_n =^?_E t_n\}
$$

of equations between $F$-terms. An *$E$-unifier* of $\Gamma$ is a substitution $\sigma$ with $s_i\sigma =_E t_i\sigma$ for all $i$, and $\Gamma$ is *$E$-unifiable* if it has one. Its *cardinality* is the number $n$ of equations.

**Kinds of problems.** $\Gamma$ is an *elementary* $E$-unification problem if $F = \mathrm{Sig}(E)$; an $E$-unification problem *with constants* if $F \setminus \mathrm{Sig}(E)$ consists of constant symbols; and a *general* $E$-unification problem if $F \setminus \mathrm{Sig}(E)$ may contain arbitrary function symbols. *$E$-unification* (elementary, with constants, or general) is the decision problem whether a given problem of that kind is $E$-unifiable. *Matching modulo $E$* asks, for terms $s$ and $t$, whether some substitution $\sigma$ has $s\sigma =_E t$.

## Depends on

- [Equational calculus](../equational-logic/equational-calculus.md)

## Proof depends on

None.

## Expansion

Syntactic unification is the case $E = \emptyset$. For general unification a system of equations reduces to a single equation by a fresh function symbol, $f(s_1, \dots, s_n) =^?_E f(t_1, \dots, t_n)$, but for elementary unification and unification with constants systems and single equations may behave differently. Matching modulo $E$ reduces to unification with constants by replacing the variables of $t$ with fresh constants. The decidability of $E$-unification can depend on the kind of problem considered, which is why results always name the kind.

## Sources

- F. Baader and W. Snyder, "Unification theory", in A. Robinson and A. Voronkov (eds.), *Handbook of Automated Reasoning*, Vol. I, Elsevier, 2001, Chapter 8, pp. 445–533, doi:10.1016/B978-044450813-3/50010-2; read in the authors' open-access copy at <https://lat.inf.tu-dresden.de/research/papers/2001/BaaderSnyderHandbook.pdf>: Section 3.1 (Definition 3.1), Section 3.2.2 (Definition 3.9), Section 3.2.3, Section 7 (matching).
