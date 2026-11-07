# Banker's safety algorithm

Let $S$ be a system of claims and allocations with processes
$P$ and a finite set $R$ of resource types. Given a free resource vector $w : R \to \mathbb{N}$
and a list of pending processes, the algorithm fails if the list has a repetition. Otherwise it
runs the safety algorithm with fuel equal to the length of the list: it repeatedly lets the
first pending process whose remaining need (claim minus allocation, truncated at zero) is at
most the free resources componentwise finish and adds its allocation to the free resources,
for at most one round per pending process, and it succeeds exactly when no pending process is
left at the end.
