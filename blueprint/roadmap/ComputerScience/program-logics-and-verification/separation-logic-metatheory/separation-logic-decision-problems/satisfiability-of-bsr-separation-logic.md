# Satisfiability of Bernays–Schönfinkel–Ramsey separation logic is undecidable

Separation logic over heaps whose cells hold $k \ge 2$ record fields, restricted to prenex sentences with an $\exists^*\forall^*$ quantifier prefix but with unrestricted separating conjunctions and implications, has an undecidable satisfiability problem over finite universes and over infinite universes alike, unlike the corresponding fragment of first-order logic.

**Setting (Echenim, Iosif and Peltier).** For an integer $k \ge 1$, the formulas of $\mathsf{SL}^k$ are built from $\bot$, $\top$, $\mathsf{emp}$, equalities $x = y$ and points-to atoms $x \mapsto (y_1, \dots, y_k)$ with $\wedge$, $\neg$, the separating conjunction $*$, the separating implication $-\!\!*$ and $\exists$. They are interpreted over structures $(U, s, h)$ with a countable universe $U$ of locations, a store $s$ mapping variables to locations, and a *heap* $h$, a finite partial map $U \rightharpoonup U^k$: $\mathsf{emp}$ holds when $h$ is empty, $x \mapsto (y_1, \dots, y_k)$ holds when $h$ is the single cell $s(x) \mapsto (s(y_1), \dots, s(y_k))$, $\varphi_1 * \varphi_2$ holds when $h$ splits into disjoint heaps satisfying $\varphi_1$ and $\varphi_2$, and $\varphi_1 -\!\!* \varphi_2$ holds when every disjoint heap satisfying $\varphi_1$, added to $h$, gives a heap satisfying $\varphi_2$. The *Bernays–Schönfinkel–Ramsey fragment* $\mathsf{BSR}(\mathsf{SL}^k)$ consists of the sentences $\exists x_1 \dots \exists x_n\, \forall y_1 \dots \forall y_m\; \varphi$ with $\varphi$ a quantifier-free $\mathsf{SL}^k$ formula. *Finite* (respectively *infinite*) *satisfiability* asks whether a sentence has a model with $U$ finite (respectively infinite).

**Theorem (Echenim, Iosif and Peltier).** For every $k \ge 2$, the finite satisfiability problem and the infinite satisfiability problem for $\mathsf{BSR}(\mathsf{SL}^k)$ are undecidable.

The same paper defines two subsets of $\mathsf{BSR}(\mathsf{SL}^k)$, by restricting universally quantified variables under separating implications and the polarity of those implications, for which finite and infinite satisfiability respectively are PSPACE-complete.

## Depends on

- [Heap assertion](../../separation-logic/hassertion.md)

## Proof depends on

None.

## Expansion

The proof reduces finite satisfiability of the first-order class of sentences $\forall x\, \phi(x)$ with $\phi$ a quantifier-free Boolean combination of equations between terms built from two unary function symbols $f$, $g$, the variable $x$ and a constant $c$; this class has an undecidable finite satisfiability problem (Börger, Grädel and Gurevich). After flattening nested terms, each term $f(x_i)$ and $g(x_i)$ is represented by the two fields of a heap cell at $x_i$, so the two functions become a heap with $k = 2$ fields; a universal formula then states that every allocated cell satisfies the flattened matrix, and an extra conjunct forces every location to be allocated (for finite models) or every pointed-to location to be allocated (for infinite models). The resulting $\mathsf{BSR}(\mathsf{SL}^2)$ sentence has a finite, respectively infinite, model exactly when the original sentence has a finite model. A good expansion adds and links a page for the undecidability of finite satisfiability of this first-order class.

## Sources

- Mnacho Echenim, Radu Iosif and Nicolas Peltier, *The Bernays-Schönfinkel-Ramsey Class of Separation Logic on Arbitrary Domains*, Foundations of Software Science and Computation Structures (FoSSaCS 2019), Lecture Notes in Computer Science 11425, Springer, 2019, pp. 242–259, https://doi.org/10.1007/978-3-030-17127-8_14; the definition of $\mathsf{SL}^k$ in Section 2 and the undecidability theorem for $\mathsf{BSR}(\mathsf{SL}^k)$ with its proof, read in the extended version arXiv:1802.00195v2. Locators in arXiv:1802.00195v2: Theorem 1 (Section 5.1).
