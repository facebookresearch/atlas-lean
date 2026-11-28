# Polynomial rings over integral domains are existentially undecidable

For every integral domain $R$, the existential theory of the polynomial ring $R[t]$ in the language of rings with a constant for $t$ is undecidable; Denef proved this for characteristic zero and for positive characteristic.

Let $R$ be an integral domain and $R[t]$ the polynomial ring in one variable over $R$. Consider the language $\mathcal{L}_{\mathrm{ring}} \cup \{t\} = \{+, \cdot, 0, 1, t\}$, where the constant $t$ is interpreted as the variable of $R[t]$. The *existential theory* of $R[t]$ in this language is the set of sentences $\exists x_1 \cdots \exists x_n\, \varphi$, with $\varphi$ quantifier-free, that are true in $R[t]$.

**Theorem (Denef).** For every integral domain $R$, the existential theory of $R[t]$ in $\mathcal{L}_{\mathrm{ring}} \cup \{t\}$ is undecidable. In particular this holds for $\mathbb{C}[t]$.

The ring $R$ is arbitrary and fixed; only the existential sentence is the input, and its only constants are $0$, $1$ and $t$. For $R$ of characteristic zero this is the result of Denef's 1978 paper, and for $R$ of positive characteristic that of his 1979 paper. Over the field of fractions the situation is different: for $\mathbb{C}(t)$ Hilbert's tenth problem is open, while for $\mathbb{R}(t)$ it has a negative answer. Over $\mathbb{F}_q[t]$ the stronger statement holds that every recursively enumerable set is Diophantine ([Demeyer](recursively-enumerable-sets-over-fq-t-diophantine.md)).

## Depends on

- [Commutative ring with identity](../../../Algebra/rings-and-fields/commutative-ring-with-identity.md)

## Proof depends on

None.

## Expansion

The sources read state the theorem without proof. For the function fields $\mathbb{R}(t)$ and $\mathbb{C}(t_1, t_2)$, Koenigsmann describes the route of an existential definition of $\mathbb{Z}$ followed by the Davis–Putnam–Robinson–Matiyasevich theorem; in positive characteristic, where $\mathbb{Z}$ is not a subset of the ring, the integers have to be interpreted existentially instead. A good expansion links the result the proof reduces from (the undecidability of Hilbert's tenth problem over $\mathbb{Z}$, or of the corresponding existential theory of the integers with addition and a divisibility-type relation in positive characteristic) together with the existential definition or interpretation of the integers in $R[t]$ that Denef constructs, which has no page.

## Sources

- Jochen Koenigsmann, *Undecidability in number theory*, in: Model Theory in Algebra, Analysis and Arithmetic, Lecture Notes in Mathematics 2111, Springer, 2014, pp. 159–195, https://doi.org/10.1007/978-3-642-54936-6_5; read as arXiv:1309.0441v1: Section 5.3 (Open problems) of arXiv:1309.0441v1, which states that $R[t]$ for any integral domain $R$ is existentially undecidable in $\mathcal{L}_{\mathrm{ring}} \cup \{t\}$, crediting the two papers below, and Section 5.2 for the function-field cases recalled in prose.
- Jeroen Demeyer, *Recursively enumerable sets of polynomials over a finite field are Diophantine*, Inventiones Mathematicae 170 (2007), no. 3, 655–670, https://doi.org/10.1007/s00222-007-0078-6; read in the author's open-access copy of the journal version at https://biblio.ugent.be/publication/389620/file/1136560.pdf: the introduction, which states that $R[Z]$ is undecidable for every integral domain $R$ of characteristic $p > 0$ by Denef's 1979 paper.
- Jan Denef, *The Diophantine problem for polynomial rings and fields of rational functions*, Transactions of the American Mathematical Society 242 (1978), 391–399, https://doi.org/10.1090/S0002-9947-1978-0491583-7: the characteristic zero case (not read; cited beside the sources above).
- Jan Denef, *The Diophantine problem for polynomial rings of positive characteristic*, in: M. Boffa, D. van Dalen and K. McAloon (eds.), Logic Colloquium '78, Studies in Logic and the Foundations of Mathematics 97, North-Holland, 1979, pp. 131–145, https://doi.org/10.1016/S0049-237X(08)71623-9: the positive characteristic case (not read; cited beside the sources above).
