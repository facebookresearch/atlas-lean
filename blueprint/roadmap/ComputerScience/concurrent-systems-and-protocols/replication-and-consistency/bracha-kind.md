# Message kinds of Bracha's broadcast

A message of Bracha's protocol is a pair $(k, v)$
of a kind $k$ and a value $v$: the leader's proposal $\langle v\rangle$ (kind `init`), an echo
$\langle \mathrm{echo}, v\rangle$ (kind `echo`) or a vote $\langle \mathrm{vote}, v\rangle$
(kind `vote`).
