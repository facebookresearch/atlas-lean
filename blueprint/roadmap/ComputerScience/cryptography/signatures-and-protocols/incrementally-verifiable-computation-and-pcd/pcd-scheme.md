# Proof-carrying data for a compliance predicate

Let $\varphi$ be a polynomial-time *compliance predicate* taking a message $z$, local data $w$ and incoming messages $z_1,\dots,z_m$. A *transcript* is a directed acyclic graph whose vertices carry local data and whose edges carry messages; it is *$\varphi$-compliant* if, at every vertex, $\varphi(z_{\mathrm{out}},w,z_{\mathrm{in},1},\dots,z_{\mathrm{in},m})=1$. A *proof-carrying data (PCD) system* $(\mathsf{G},\mathsf{P},\mathsf{V})$ lets each vertex, given incoming messages with proofs $(z_j,\pi_j)$ and local data $w$, produce a proof $\pi$ for its outgoing message $z$, such that (completeness) honest proofs of $\varphi$-compliant transcripts verify, and (knowledge soundness) from any efficient prover outputting an accepted $(z,\pi)$ one can extract a $\varphi$-compliant transcript ending in $z$. IVC is the special case where the graph is a path and $\varphi(z_{\mathrm{out}},w,z_{\mathrm{in}})$ checks $z_{\mathrm{out}}=F(z_{\mathrm{in}},w)$.

## Depends on

- [Incrementally verifiable computation scheme for an iterated function](ivc-scheme.md)

## Sources

- Alessandro Chiesa, Eran Tromer, "Proof-Carrying Data and Hearsay Arguments from Signature Cards", ICS (2010).
- Nir Bitansky, Ran Canetti, Alessandro Chiesa, Eran Tromer, "Recursive Composition and Bootstrapping for SNARKs and Proof-Carrying Data", STOC (2013).
