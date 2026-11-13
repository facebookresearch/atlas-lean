# Static CCS processes

Finite CCS processes with the static operators, over a type of
channel names, are built from the inactive process $0$ by the prefix $\alpha.P$ of a CCS action
$\alpha$ (silent, an input or an output) and a process $P$, the choice $P + Q$, the parallel
composition $P \mid Q$, the restriction $P \setminus L$ of $P$ by a finite list $L$ of names, and
the relabelling $P[f]$ of $P$ by a finite relabelling $f$.

Unlike function-valued operators, finite lists and tables preserve decidable
equality of processes and cannot express relabellings that alter the silent action $\tau$ or fail
to preserve complementary visible actions.
