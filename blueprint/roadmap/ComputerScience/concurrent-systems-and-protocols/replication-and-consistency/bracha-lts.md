# Bracha's broadcast as a transition system

Let $n$ be the number of parties, $f$ a
natural number, `leader` the designated leader and $F$ the set of faulty parties. A stuttering
step (label `none`) changes nothing. A step labelled $(q, i, (k, v))$ lets a non-faulty party $i$
receive the message $(k, v)$ from $q$ for the first time. It is possible when $q$ has sent
$(k, v)$ to $i$, or when $q$ is faulty: a faulty party may send any message to anyone at any
time, but only under its own name, as the channels are authenticated. Let $r$ be the messages
$i$ has received, this one included. In the step, $i$
* echoes $v$, sending $(\mathrm{echo}, v)$ to every party, if it has not echoed yet, $k$ is
  `init` and $q$ is the leader;
* votes for $v$, sending $(\mathrm{vote}, v)$ to every party, if it has not voted yet and $r$
  holds $(\mathrm{echo}, v)$ from at least $n - f$ parties or $(\mathrm{vote}, v)$ from at least
  $f + 1$ parties;
* delivers $v$ if it has not delivered yet and $r$ holds $(\mathrm{vote}, v)$ from at least
  $n - f$ parties.

Nothing else changes. Here $n - f$ is truncated subtraction, $0$ when $f \ge n$.
