# Greedy scan with an independence oracle

Given an oracle $O$ that accepts or rejects each
finite subset of a type $\alpha$, a finite set $S \subseteq \alpha$ and a list $e_1, \dots, e_n$ of
elements of $\alpha$, the greedy scan processes $e_1, \dots, e_n$ in order, starting with $S$ as
the current set: it replaces the current set $T$ by $T \cup \{e_i\}$ if $O$ accepts
$T \cup \{e_i\}$, and leaves it unchanged otherwise. It returns the final current set and charges
one unit of time per element processed.
