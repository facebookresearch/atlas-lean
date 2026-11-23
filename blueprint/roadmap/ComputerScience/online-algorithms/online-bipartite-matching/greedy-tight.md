# The ratio one half is tight for greedy

For every $n$, some sequence of $2n$ arrivals on $2n$ left vertices has a perfect matching $m$ with
$|m| = 2n$ of which the greedy online matcher matches exactly half: $2 \cdot \mathrm{ALG} = |m|$, where
$\mathrm{ALG}$ is the number of arrivals greedy matches. Since greedy satisfies $|m| \le 2 \cdot \mathrm{ALG}$
on every sequence of arrivals with a perfect matching $m$, the ratio $1/2$ is tight for greedy. Greedy is
moreover optimal among deterministic online matchers, by a separate adversary result: against every
deterministic online matcher on $2n$ left vertices, some sequence of $2n$ arrivals has a perfect matching
of size $2n$ while the matcher matches at most $n$ arrivals.
