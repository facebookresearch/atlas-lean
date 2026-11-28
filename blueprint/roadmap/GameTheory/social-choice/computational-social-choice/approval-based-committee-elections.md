# Approval-based committee elections

An approval election has a finite set $N$ of $n \ge 1$ voters, a finite set $C$ of candidates, approval sets $A_i \subseteq C$ (possibly empty)
and a committee size $k$ with $1 \le k \le \lvert C \rvert$. A committee is a $k$-subset $W$ of $C$. Approval voting (AV) selects committees
maximizing $\sum_i \lvert A_i \cap W \rvert$; satisfaction approval voting (SAV) maximizes $\sum_{i : A_i \ne \emptyset} \lvert A_i \cap W \rvert / \lvert A_i \rvert$ (voters with empty ballots, for whom the ratio is undefined, contribute nothing);
proportional approval voting (PAV) maximizes $\sum_i H(\lvert A_i \cap W \rvert)$ with $H(j) = \sum_{\ell = 1}^{j} 1/\ell$; minimax approval
voting (MAV) minimizes $\max_i \lvert A_i \triangle W \rvert$; GreedyAV starts
with $W = \emptyset$ and repeatedly adds a candidate approved by the largest number of voters who approve no member of $W$, filling
the remaining seats arbitrarily once no such voter remains. Each rule is resolute only after a stated tie-breaking order.

## Sources

- H. Aziz, M. Brill, V. Conitzer, E. Elkind, R. Freeman and T. Walsh, *Justified Representation in Approval-Based Committee Voting*, Soc. Choice Welf. 48 (2017), §2 (the model) and §2.1 (the rules AV, SAV, PAV, GreedyAV and MAV, and the deterministic tie-breaking convention), in the authors' journal copy. <https://cgi.cse.unsw.edu.au/~haziz/rep_journal.pdf>
