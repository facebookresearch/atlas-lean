# Kripke completeness of intuitionistic first-order logic

This node covers intuitionistic first-order logic (IQC) for relational languages and its soundness
and completeness for Kripke models with expanding domains.

Let $L$ be a first-order language with relation symbols only, no function symbols or constants,
and let formulas use $\wedge$, $\vee$, $\to$, $\bot$, $\forall$ and $\exists$ as primitives. A Kripke
structure for $L$ is a partially ordered set $(K, \le)$ of nodes with a domain function assigning to
each node $k$ a nonempty set $D(k)$, such that $D(k) \subseteq D(k')$ whenever $k \le k'$, and with
interpretations of the relation symbols at each node that grow along $\le$. Forcing of a formula at
a node is defined relative to an assignment of elements of $D(k)$ to its free variables, as in the
propositional case, with $k$ forcing $\exists x\, \varphi$ when it forces $\varphi$ for some value of
$x$ in $D(k)$, and $k$ forcing $\forall x\, \varphi$ when every $k' \ge k$ forces $\varphi$ for every
value of $x$ in $D(k')$. The cited survey states the main result for sentences: a sentence is
derivable in IQC exactly when it is forced at every node of every Kripke structure. The form for a
finite set $\Gamma$ of formulas and a formula $\varphi$, possibly with free variables (for every
Kripke structure, every node $k$ and every assignment into $D(k)$, if $k$ forces all members of
$\Gamma$ under the assignment then it forces $\varphi$ under it), is an obligation of the expansion,
not a statement taken from that source.

## Expansion

A sound expansion has separate pages for: the syntax and a derivation system of IQC; Kripke
structures with expanding domains and forcing under assignments, with persistence; soundness;
completeness for sentences, as in the cited survey; and completeness for finite sets of formulas
with free variables under assignments, which needs its own source or proof.
Constant-domain semantics validates additional principles and must not replace expanding domains.
Languages with equality or function symbols need a separately justified extension (the cited survey
interprets equality at each node by an equivalence relation, subject to persistence) and are outside
this node.

## Sources

- J. Moschovakis, *Intuitionistic logic*, Stanford Encyclopedia of Philosophy, substantive revision 16 December 2022, §5.1. <https://plato.stanford.edu/entries/logic-intuitionistic/>
