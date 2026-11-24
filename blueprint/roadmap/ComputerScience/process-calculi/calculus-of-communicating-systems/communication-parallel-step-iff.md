# Transitions of a parallel composition

For CCS processes $P$, $Q$, $R$ and a CCS label $a$,
the parallel composition $P \mid Q$ has a transition labelled $a$ to $R$ in the CCS transition
relation with communication if and only if one of the following holds: $P$ has a transition
labelled $a$ to some $P'$ and $R = P' \mid Q$; or $Q$ has a transition labelled $a$ to some $Q'$
and $R = P \mid Q'$; or $a = \tau$ and there are processes $P'$, $Q'$ and complementary labels
$b$, $c$ such that $P$ has a transition labelled $b$ to $P'$, $Q$ has a transition labelled $c$
to $Q'$, and $R = P' \mid Q'$.
