# Characteristic polynomial of the dual of a linear endomorphism

This node is still to be broken down. Let $\mathcal{O}$ be a commutative ring and $A$ a finite locally free
$\mathcal{O}$-algebra such that $\operatorname{Hom}_{\mathcal{O}}(A, \mathcal{O})$ is a locally free $A$-module (necessarily
of rank $1$). Let $M$ be a finite locally free $A$-module and $M^* = \operatorname{Hom}_{\mathcal{O}}(M, \mathcal{O})$, with
the $A$-module structure $(a \varphi)(m) = \varphi(am)$; then $M^*$ is a finite locally free $A$-module of the same
rank as $M$. For every $A$-linear map $f \colon M \to M$, the $\mathcal{O}$-dual
$f^* \colon M^* \to M^*$, $\varphi \mapsto \varphi \circ f$, is $A$-linear, and the characteristic polynomials of $f$ and $f^*$
over $A$ agree:

$$\operatorname{char}_A(f) = \operatorname{char}_A(f^*) \quad \text{in } A[T].$$

## Proof depends on

Its proof uses the inputs listed in the expansion note.

## Expansion

This node is still to be broken down. A good expansion states and links, following Conrad's proof:

- the reduction to a local ring $\mathcal{O}$, so that $A$ is semilocal, and the faithfully flat base change to the
  henselization of $\mathcal{O}$ (or its completion, after reduction to the noetherian case), after which $A$ is a
  product of local rings, and then to $A$ local;
- for $A$ local, $M = \bigoplus_i A e_i$ free and an isomorphism $h \colon A \cong \operatorname{Hom}_{\mathcal{O}}(A, \mathcal{O})$
  of $A$-modules, the dual basis $e_i^* = h(1) \circ \pi_i$ of $M^*$ built from the coordinate projections
  $\pi_i \colon M \to A$, in which $\operatorname{Mat}_{\{e_i\}}(f) = \operatorname{Mat}_{\{e_i^*\}}(f^*)^{t}$;
- the invariance of the characteristic polynomial under transposition and under base change.

## Sources

- B. Conrad, "The Shimura construction in weight 2", appendix to K. A. Ribet and W. A. Stein,
  *Lectures on Serre's conjectures*, IAS/Park City Mathematics Series; page numbers are those of the
  authors' text at <https://wstein.org/edu/Fall2003/252/references/ribet-stein-serre/ribet-stein.pdf>:
  §5.3, Lemma 5.17 and its proof, p. 71 ("Let $\mathcal{O}$ be a commutative ring, $A$ a finite locally free
  $\mathcal{O}$-algebra with $\operatorname{Hom}_{\mathcal{O}}(A, \mathcal{O})$ a locally free $A$-module (necessarily of rank 1).
  Let $M$ be a finite locally free $A$-module, $M^* = \operatorname{Hom}_{\mathcal{O}}(M, \mathcal{O})$, so $M^*$ is finite and
  locally free over $A$ with the same rank as $M$. For any $A$-linear map $f \colon M \to M$ with $\mathcal{O}$-dual
  $f^* \colon M^* \to M^*$, automatically $A$-linear, $\operatorname{char}(f) = \operatorname{char}(f^*)$ in $A[T]$ (these are the
  characteristic polynomials)").
