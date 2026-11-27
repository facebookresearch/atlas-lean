# Soundness of the recursion rule

Commands are atomic nondeterministic actions $\mathbf{do}\ f$ (with $f$ mapping each state to a set of successor states), sequencing,
conditionals, loops and $\mathbf{call}$ of a single parameterless procedure with body $\mathit{body}$. The big-step relation $s \xrightarrow{c} t$ is
defined inductively, with $s \xrightarrow{\mathbf{call}} t$ whenever $s \xrightarrow{\mathit{body}} t$. The depth-indexed relation $s \xrightarrow{c}_n t$ is
defined by the same rules except that $s \xrightarrow{\mathbf{call}}_{n+1} t$ whenever $s \xrightarrow{\mathit{body}}_n t$; it is monotone in $n$, and
$s \xrightarrow{c} t$ holds exactly when $s \xrightarrow{c}_n t$ for some $n$.

Assertions $P(z, s)$ depend on an auxiliary state $z$ and the program state $s$. A triple $\{P\}\,c\,\{Q\}$ is *valid* if
$s \xrightarrow{c} t$ and $P(z, s)$ imply $Q(z, t)$ for all $z$, and *valid at depth* $n$ if the same holds for $\xrightarrow{c}_n$. Judgements
$C \vdash \{P\}\,c\,\{Q\}$ carry a context $C$ of assumed triples, and $C \models \{P\}\,c\,\{Q\}$ means that validity of every triple of $C$
implies validity of $\{P\}\,c\,\{Q\}$ (similarly at depth $n$). Besides the rules for actions, sequencing, conditionals, loops and the
consequence rule, the system has the recursion rule and the assumption rule:

$$\frac{\{(P, \mathbf{call}, Q)\} \vdash \{P\}\,\mathit{body}\,\{Q\}}{\emptyset \vdash \{P\}\,\mathbf{call}\,\{Q\}} \qquad \{(P, \mathbf{call}, Q)\} \vdash \{P\}\,\mathbf{call}\,\{Q\}.$$

**Theorem.** If $C \vdash \{P\}\,c\,\{Q\}$ then $C \models_n \{P\}\,c\,\{Q\}$ for every $n$, by induction on the derivation; for the recursion rule,
validity of the call at depth $n$ follows by induction on $n$, depth $0$ being vacuous. Consequently every derivable judgement is
valid: $C \vdash \{P\}\,c\,\{Q\}$ implies $C \models \{P\}\,c\,\{Q\}$.

## Sources

- T. Nipkow, "Hoare logics for recursive procedures and unbounded nondeterminism", *Computer Science Logic (CSL 2002)*, LNCS 2471, Springer, 2002, <https://www21.in.tum.de/~nipkow/pubs/csl02.pdf>: Section 2 (both semantics, monotonicity and lemma exec-iff-execn) and Section 3 (validity, the proof system and the soundness theorem). All proofs are checked in Isabelle/HOL.
- K. R. Apt, F. S. de Boer and E.-R. Olderog, *Verification of Sequential and Concurrent Programs*, 3rd ed., Springer, 2009.
