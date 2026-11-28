# Bounded arithmetic with mod p counting collapses to approximate counting

For a prime $p$, full bounded arithmetic $T_2(\oplus_p)$ with mod $p$ counting quantifiers is conservative over the approximate counting theory $APC_2^{\oplus_p P}$, which proves a form of Toda's theorem: every bounded formula with counting quantifiers defines a $BP \cdot \oplus_p P$ property. So the hierarchy of these theories collapses to $T_2^{3, \oplus_p P}$.

Fix a prime $p$ and write $[p] = \{0, 1, \dots, p-1\}$. The language contains all $PV_1$ function and predicate symbols (one for each polynomial-time function and relation) and, for each $k \in [p]$, a **counting quantifier** $(C^k_p x \le t) A(x)$, meaning that the number of $x \le t$ with $A(x)$ is congruent to $k$ modulo $p$ (residues are read modulo $p$). The quantifiers are governed by the initial sequents $A(0) \to (C^1_p x \le 0) A(x)$, $\neg A(0) \to (C^0_p x \le 0) A(x)$, $A(t+1) \wedge (C^k_p x \le t) A(x) \to (C^{k+1}_p x \le t+1) A(x)$, $\neg A(t+1) \wedge (C^k_p x \le t) A(x) \to (C^k_p x \le t+1) A(x)$, and $\neg[(C^k_p x \le t) A(x) \wedge (C^{\ell}_p x \le t) A(x)]$ for $k \ne \ell$ modulo $p$. Counting quantifiers count as bounded, and $\Sigma^b_\infty(\oplus_p)$ is the set of bounded formulas.

- $T_2(\oplus_p)$ is axiomatized by the defining axioms of the $PV_1$ symbols, the counting initial sequents and induction for all bounded formulas.
- A $\oplus_p P$ formula is atomic or of the form $(C^k_p x \le t) A(x)$ with $A$ sharply bounded. $\Sigma^{b, \oplus_p P}_0$ is the closure of these under Boolean connectives and sharply bounded quantifiers, and $\Sigma^{b, \oplus_p P}_i$ counts alternations of bounded quantifiers in front. $T_2^{i, \oplus_p P}$ is axiomatized by the $PV_1$ axioms, the counting initial sequents for sharply bounded $A$, and $\Sigma^{b, \oplus_p P}_i$ induction.
- $APC_2^{\oplus_p P} = T_2^{1, \oplus_p P} + sWPHP(PV_2^{\oplus_p P})$, where $PV_2^{\oplus_p P}$ is the class of functions computable in polynomial time relative to $NP^{\oplus_p P}$, and $sWPHP(F)$ is the surjective weak pigeonhole principle for $f \in F$: for $x > 0$ and all $y$ there is $v \le x(|y|+1)$ with $f(u) \ne v$ for every $u \le x|y|$.
- With $\oplus^k_p\mathrm{Sat}$ the set of propositional formulas whose number of satisfying assignments is congruent to $k$ modulo $p$, a language $L$ is in $BP \cdot \oplus_p P$ if there are $PV_1$ functions $f$ and $u$ with $x \in L$ iff $\Pr_{r < u(x)}[f(x, r) \notin \oplus^1_p\mathrm{Sat}] \preceq_0 1/4$, and $x \notin L$ iff $\Pr_{r < u(x)}[f(x, r) \notin \oplus^0_p\mathrm{Sat}] \preceq_0 1/4$, where $\preceq_0$ is the $\epsilon=0$ case of Jeřábek's approximate comparison $\preceq_\epsilon$ (Definition 34, equations (21)–(22)).

**Theorem.** Let $p$ be prime. $T_2(\oplus_p)$ is conservative over $APC_2^{\oplus_p P}$: every formula of the language of $APC_2^{\oplus_p P}$ provable in $T_2(\oplus_p)$ is provable in $APC_2^{\oplus_p P}$. Furthermore, $T_2(\oplus_p)$ proves that every $\Sigma^b_\infty(\oplus_p)$ formula defines a property in $BP \cdot \oplus_p P$.

**Corollary.** Since $APC_2^{\oplus_p P} \subseteq T_2^{3, \oplus_p P} \subseteq T_2(\oplus_p)$, the theory $T_2(\oplus_p)$ is conservative over $T_2^{3, \oplus_p P}$.

## Expansion

Nesting costs nothing at the bottom: $\oplus_p P^{\oplus_p P} \subseteq \oplus_p P$ for $p$ prime, by a direct simulation that guesses the answers to parity queries and uses Fermat's little theorem to make wrong guesses cancel modulo $p$, and this is formalizable in $PV_1^{\oplus_p P}$. Inside $APC_2^{\oplus_p P}$ the Valiant–Vazirani isolation lemma is formalized with Jeřábek's approximate counting, giving that every $\Sigma^b_1$ property, and then every $\exists \cdot \oplus_p P$ property, is in $BP \cdot \oplus_p P$.

The proof assigns to each $\Sigma^b_\infty(\oplus_p)$ formula $\varphi$ a translation $\langle f_\varphi, u_\varphi \rangle$ by induction on $\varphi$; $APC_2^{\oplus_p P}$ verifies that each translation represents a $BP \cdot \oplus_p P$ property, that translations commute with connectives and bounded quantifiers up to provable equivalence, and that the counting initial sequents hold after translation. Induction for $BP \cdot \oplus_p P$ properties is already available there, so every $T_2(\oplus_p)$ proof translates into an $APC_2^{\oplus_p P}$ proof. The argument relativizes to added oracle predicates, the form used for the propositional collapse.

## Depends on

None.

## Proof depends on

None.

## Sources

- Sam Buss, Leszek Aleksander Kołodziejczyk, Konrad Zdanowski, "Collapsing modular counting in bounded arithmetic and constant depth propositional proofs", *Transactions of the American Mathematical Society*, 2015, doi:10.1090/S0002-9947-2015-06233-3 (Theorem 39 and Corollaries 40 and 41; definitions of $T_2(\oplus_p)$, $\oplus_p P$ formulas and $T_2^{i, \oplus_p P}$ in Section 2.2 (Definitions 16 and 17 and the unnumbered paragraph after Definition 17; Definition 19 defines $T_2^{i,\sigma_p}$), of $APC_2^{\oplus_p P}$ in Section 2.3 and of $BP \cdot \oplus_p P$ in Definition 34; Theorem 20, Lemma 32 (Valiant–Vazirani) and Lemmas 35 and 38 for the proof in Section 4.3; numbering of the authors' public manuscript in the journal's format, https://mathweb.ucsd.edu/~sbuss/ResearchWeb/TodaAndParityFrege/modcounting-ams.pdf).
