# An ML fragment with integer references

Types are $ty ::= \mathrm{bool} \mid \mathrm{int} \mid \mathrm{unit} \mid ty * ty \mid ty \to ty \mid \mathrm{int\ ref}$. Expressions are those of a call-by-value ML: value identifiers, booleans
with $\mathrm{if}$, integers with $=$, $+$, $-$, $()$, look-up $!e$, assignment $e := e$, storage creation $\mathrm{ref}\ e$, location equality $e == e$, sequencing, pairs with
$\mathrm{fst}$ and $\mathrm{snd}$, abstraction $\mathrm{fun}(x : ty) \to e$, recursive functions $\mathrm{fun}\ f = (x : ty) \to e$, application and $\mathrm{let}$, plus names $\ell$ of storage locations
drawn from a countably infinite set $\mathrm{Loc}$. A *state* $s$ is a finite map from locations to integers. Canonical forms are constants, $()$, locations, pairs of canonical
forms and the two kinds of function.

The *evaluation relation* $s, e \Rightarrow v, s'$ (closed $e$, closed canonical $v$, $\mathrm{loc}(e) \subseteq \mathrm{dom}(s)$ and $\mathrm{loc}(v) \subseteq \mathrm{dom}(s')$, where $\mathrm{loc}(e)$ is the set of locations occurring in $e$; evaluation then gives $\mathrm{dom}(s) \subseteq \mathrm{dom}(s')$) is defined inductively in the style of the Definition of
Standard ML, with the environment substituted in; for example $s, \mathrm{let}\ x = e_1\ \mathrm{in}\ e_2 \Rightarrow v, s''$ when $s, e_1 \Rightarrow v_1, s'$ and
$s', e_2[v_1/x] \Rightarrow v, s''$, and $\mathrm{ref}\ e$ allocates a fresh location. Type assignment $\Gamma \vdash e : ty$ is syntax-directed, the programs of type $ty$ are
$\mathrm{Prog}_{ty} = \{e : \emptyset \vdash e : ty\}$, and evaluation preserves types: if $s, e \Rightarrow v, s'$ and $\emptyset \vdash e : ty$ then $\emptyset \vdash v : ty$.

## Sources

- A. M. Pitts, "Operational semantics and program equivalence", in G. Barthe, P. Dybjer, L. Pinto and J. Saraiva (eds.), *Applied Semantics*, LNCS 2395, Springer, 2002, 378–412, <https://doi.org/10.1007/3-540-45699-6_8>: Section 3 (Figures 2 and 3) and Appendix A, Sections A.1–A.4 (types, expressions, evaluation relation, type assignment and Theorem A.1, type soundness).
