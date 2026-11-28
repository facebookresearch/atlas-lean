# Liveness and configuration reachability of order-2 asynchronous programs are undecidable

For asynchronous programs whose handlers post tasks according to languages of higher-order recursion schemes of order 2, configuration reachability, fair non-termination and fair starvation are undecidable, although safety, termination and boundedness are decidable for higher-order recursion schemes of every order.

**Setting (Majumdar, Thinniyam and Zetzsche).** A *full trio* is a class of languages closed under intersection with regular languages, homomorphic images and inverse homomorphic images; it is *effective* if, given a language $L$ of the class, a regular language $R$ and a homomorphism $h$, representations of $L \cap R$, $h(L)$ and $h^{-1}(L)$ in the class can be computed (Section 2). Let $\mathcal{C}$ be an effective full trio of languages. An *asynchronous program* over $\mathcal{C}$ is $\mathfrak{P} = (D, \Sigma, (L_c)_{c \in D \times \Sigma \times D}, d_0, \mathbf{m}_0)$ with a finite set $D$ of global states, an alphabet $\Sigma$ of handler names, a language $L_{d \sigma d'} \in \mathcal{C}$ over $\Sigma$ for each context, an initial state $d_0$ and an initial multiset $\mathbf{m}_0$ of pending handlers. Configurations are pairs $(d, \mathbf{m})$ of a global state and a multiset over $\Sigma$, and $(d, \mathbf{m} \oplus [\sigma]) \xrightarrow{\sigma} (d', \mathbf{m} \oplus \mathbf{m}')$ whenever some $w \in L_{d \sigma d'}$ has [Parikh image](../../../../../TheoryOfComputation/context-free-languages/closure-and-pumping/parikh-images-and-semilinear-sets/parikh-image.md) $\mathbf{m}'$: a pending instance of $\sigma$ is executed and posts the handlers counted by $w$. An infinite run is *fair* if every handler that is pending at some point is executed at some later point, and a fair run *starves* $\sigma$ if from some point on $\sigma$ is always pending and is executed only when at least two instances are pending. *Configuration reachability* asks whether a given configuration is reachable from $(d_0, \mathbf{m}_0)$; *fair non-termination* asks whether some infinite run is fair; *fair starvation* asks whether some fair run starves some handler.

**Theorem (Majumdar, Thinniyam and Zetzsche).**

1. For every full trio $\mathcal{C}$, configuration reachability, fair non-termination and fair starvation for asynchronous programs over $\mathcal{C}$ are all decidable or all undecidable, and if they are decidable then it is decidable whether a language of $\mathcal{C}$ over $\{a, b\}$ contains a word with as many $a$s as $b$s.
2. For asynchronous programs over the languages of higher-order recursion schemes (word schemes), configuration reachability, fair non-termination and fair starvation are undecidable already at order 2 (Corollary 5.3).

For asynchronous programs over the languages of order-2 pushdown automata (the indexed languages) the same undecidability follows directly from clause 1 and the undecidability of the $Z$-intersection problem for indexed languages (Zetzsche); the source translates order-2 pushdown automata into order-2 word schemes in one direction only and does not claim that the two classes coincide.

## Depends on

- [Decidability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Parikh image of a language](../../../../../TheoryOfComputation/context-free-languages/closure-and-pumping/parikh-images-and-semilinear-sets/parikh-image.md)

## Proof depends on

None.

## Expansion

Clause 1 is proved by mutual reductions between the three problems and a reduction from the equal-letters problem (the $Z$-intersection problem) to configuration reachability. Clause 2 follows because the $Z$-intersection problem is undecidable for indexed languages, which are exactly the languages of order-2 pushdown automata (Zetzsche), and these translate effectively into order-2 OI grammars and then into order-2 word schemes. A good expansion links pages for higher-order recursion schemes and order-2 pushdown automata and their languages, for full trios, for the undecidability of the $Z$-intersection problem for indexed languages and for the mutual reductions of clause 1.

## Sources

- Rupak Majumdar, Ramanathan S. Thinniyam and Georg Zetzsche, *General Decidability Results for Asynchronous Shared-Memory Programs: Higher-Order and Beyond*, Logical Methods in Computer Science 18(4), 2022, https://doi.org/10.46298/lmcs-18(4:2)2022; the definitions of asynchronous programs and of their decision problems, the equivalence theorem for configuration reachability, fair termination and fair starvation, and the corollary for higher-order recursion schemes, read in arXiv:2101.08611v4. Locators in arXiv:2101.08611v4: Section 2 (full trios), Theorem 4.4 and Corollary 5.3.
