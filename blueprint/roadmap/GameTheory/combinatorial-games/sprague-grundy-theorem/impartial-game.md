# Impartial game

An impartial game consists of a type of positions, a starting position,
for each position $p$ a finite set of positions reachable from $p$ in one move, and a rank
function assigning a natural number to each position such that every move strictly decreases the
rank: if $q$ is reachable from $p$ in one move, then $\mathrm{rank}(q) < \mathrm{rank}(p)$.

Because the move sets are finite and the rank strictly decreases along moves, every play
terminates and only finitely many positions are reachable from any position, even if the type of
positions is infinite or contains unreachable positions.
