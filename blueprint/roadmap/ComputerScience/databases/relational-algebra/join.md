# Natural join

The natural join $r \bowtie s$ of finite sets of tuples $r$ and $s$ is the
set of merges of $t$ and $u$ over all pairs of tuples $t \in r$ and $u \in s$ that are
compatible, that is, agree on every attribute where both are defined. The merge of $t$ and $u$
takes the value of $t$ where $t$ is defined and the value of $u$ otherwise.
