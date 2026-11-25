# Transitions of finite CCS without communication

The transition relation
$P \xrightarrow{a} P'$ on finite CCS processes is the operational semantics of finite CCS whose
synchronization function is undefined on every pair of actions. Thus prefix and choice move as
usual, and a parallel composition $P \mid Q$ moves only by letting one of $P$ and $Q$ move;
there are no communication steps.
