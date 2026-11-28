# Fair executions of Bracha's broadcast

A sequence $s_0, s_1, \dots$ of global states is
fair for a set $F$ of faulty parties when every message sent to a non-faulty party is
eventually received: if $(p, j, m)$ is among the messages sent in some $s_k$ and $j \notin F$,
then $(p, m)$ is among the messages $j$ has received in some $s_{k'}$.
