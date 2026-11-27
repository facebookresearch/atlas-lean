# Sahlqvist correspondence

Modal formulas are built from atoms, $\bot$, $\to$ and $\Box$, with $\wedge$, $\vee$ and $\Diamond$ defined from these. A formula is positive or negative by simultaneous recursion: atoms and $\bot$ are positive, $\bot$ is negative and no atom is negative, $\varphi \to \psi$ is positive (negative) when $\varphi$ is negative (positive) and $\psi$ is positive (negative), and $\Box\varphi$ has the polarity of $\varphi$. Sahlqvist antecedents are the smallest class containing every boxed atom $\Box^k p$ ($k \ge 0$) and every negative formula and closed under $\wedge$, $\vee$ and $\Diamond$. A Sahlqvist implication is $\alpha \to \beta$ with $\alpha$ a Sahlqvist antecedent and $\beta$ positive. The Sahlqvist formulas are the smallest class containing every Sahlqvist implication, closed under $\wedge$ and $\Box$, and containing $\varphi \vee \psi$ whenever $\varphi$ and $\psi$ are Sahlqvist formulas with no atom in common. There is no outer $\Diamond$ closure and no unrestricted disjunction.

Statement: for every Sahlqvist formula $\varphi$ there is a first-order sentence $\psi$ in the frame language, whose only symbol is a binary relation $R$, such that for every set of worlds $W$ (possibly empty) and binary relation $R$ on $W$,

$$(W, R) \models \psi \iff \text{for every valuation } V \text{ on } W \text{ and every } w \in W,\ (W, R, V), w \Vdash \varphi.$$

When $W$ is empty the right-hand side holds vacuously, so $\psi$ must also hold in the empty structure. Textbook frames have a nonempty set of worlds; the textbook correspondent extends to this statement by taking its disjunction with the sentence saying that there are no worlds. The sentence $\psi$ depends only on $\varphi$, and the quantification over valuations and worlds is on the right-hand side: $\psi$ characterizes frame validity of $\varphi$, not truth in a single pointed model. Only correspondence is stated; canonicity and completeness are separate claims.

## Sources

- H. Sahlqvist, "Completeness and Correspondence in the First and Second Order Semantics for Modal Logic", in Proceedings of the Third Scandinavian Logic Symposium, North-Holland, 1975, 110-143; see also P. Blackburn, M. de Rijke, Y. Venema, Modal Logic, Cambridge University Press, 2001, §3.6.
- M. de Rijke and H. Wansing, "Proofs and Expressiveness in Alethic Modal Logic", in *A Companion to Philosophical Logic*, Blackwell, ch. 28, Theorem 2 (Sahlqvist Correspondence Theorem).
