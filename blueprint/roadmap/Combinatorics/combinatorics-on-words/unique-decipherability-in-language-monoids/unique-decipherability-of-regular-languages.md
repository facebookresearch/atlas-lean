# Unique decipherability in the monoid of regular languages is undecidable

Over every alphabet with at least two letters, no algorithm decides whether a given finite set of regular languages freely generates the submonoid it generates under concatenation of languages.

Let $\Sigma$ be a finite alphabet. The subsets of $\Sigma^*$ form a monoid under concatenation $KL=\{uv : u\in K,\ v\in L\}$, with identity $\{\varepsilon\}$. The *unique decipherability problem* in a monoid $M$ asks, given a finite subset $\{a_1,\dots,a_n\}\subseteq M$, whether it is a free generating set of the submonoid it generates, that is, whether every element of that submonoid has exactly one factorization as a product of the $a_i$.

**Theorem (Karhumäki and Saarela).** Let $\Sigma$ be an alphabet with $|\Sigma|\ge2$. There is no algorithm that decides, given finitely many regular languages $L_1,\dots,L_n\subseteq\Sigma^*$, whether $\{L_1,\dots,L_n\}$ is a free generating set of the submonoid it generates in the monoid of languages over $\Sigma$.

Conventions: the regular languages are given effectively, for example by finite automata; the theorem holds already for a binary alphabet. For finite sets of words, that is, finite collections of singleton languages, the problem is the classical code problem in the free monoid, decided by the Sardinas–Patterson algorithm. Over a unary alphabet the problem is decidable for finite and for regular languages (Choffrut and Karhumäki). Whether it is undecidable for finite collections of finite languages is left open by the source.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces from the undecidability of unique decipherability in the direct product $\{a,b\}^*\times\{c,d\}^*$ of two free monoids (Chrobak and Rytter). For $u\in\{a,b\}^*$ and $t\in\{c,d\}^*$ put

$$
L(u,t)=\mathrm{sw}(u)\cup\mathrm{sw}(t)\cup X,
$$

where $\mathrm{sw}(w)$ is the set of scattered subwords of $w$ and $X$ is the set of words over $\{a,b,c,d\}$ that contain letters of both $\{a,b\}$ and $\{c,d\}$. The map $(u,t)\mapsto L(u,t)$ is injective and preserves products (Lemma 2.2 of the source calls it an injective morphism); it is not unital, since $L(\varepsilon,\varepsilon)=\{\varepsilon\}\cup X$ rather than $\{\varepsilon\}$. Products are preserved, $L(u,t)L(u',t')=L(uu',tt')$, because $X$ absorbs every mixed product and $\varepsilon$ lies in each $L(u',t')$, and $u$ and $t$ are recovered as the longest words of $L(u,t)$ over $\{a,b\}$ and over $\{c,d\}$. A finite set of pairs therefore freely generates its submonoid iff its image does (Theorem 2.1 of the source), which gives undecidability over four letters; encoding $\{a,b,c,d\}^*$ into $\{a,b\}^*$ gives the binary case. A good expansion links the undecidability of unique decipherability in $\{a,b\}^*\times\{c,d\}^*$.

## Sources

- Juhani Karhumäki and Aleksi Saarela, "The unique decipherability in the monoid of regular languages is undecidable", *Fundamenta Informaticae* 110(1–4):197–200, 2011, doi:[10.3233/FI-2011-537](https://doi.org/10.3233/FI-2011-537); read in the author's open-access copy at <https://amsaar.gitlab.io/articles/kasa11ibarra.pdf>: Section 1 (the problem and the known decidable cases), Section 2 (Lemma 2.1, the morphism (1) and Lemma 2.2, and Theorem 2.1), and the concluding remark on finite languages.
- Marek Chrobak and Wojciech Rytter, "Unique decipherability for partially commutative alphabet", *Fundamenta Informaticae* 10(3):323–336, 1986, the source of Lemma 2.1, as cited in the source above; not read here.
