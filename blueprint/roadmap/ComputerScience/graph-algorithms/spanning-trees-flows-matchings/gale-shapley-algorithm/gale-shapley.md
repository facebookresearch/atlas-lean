# Deferred acceptance

Let each of $n$ proposers rank the $n$ receivers, and each receiver
rank the $n$ proposers, with rank $0$ the best. Deferred acceptance is the state reached from the
initial state, in which no one has proposed and no receiver holds anyone, by repeating the
following step at most $n^2$ times, stopping early once no proposer is both free and has made
fewer than $n$ proposals: the least such proposer, having made $p$ proposals so far, proposes to
the receiver of rank $p$ in his ranking, and she then holds whichever of him and her current
holder she ranks better, or him if she held no one.

These $n^2$ steps always suffice: in the resulting state no proposer is both free and has made
fewer than $n$ proposals.
