# Synchronization of CCS labels

Let the names form a type with decidable equality. For
labels $a$ and $b$, the synchronization of $a$ with $b$ is the silent action $\tau$ when $a$ is
the input on a name $n$ and $b$ is the output on the same name $n$, or when $a$ is the output on
$n$ and $b$ is the input on $n$. For every other pair of labels, including any pair involving
$\tau$, there is no result.

This partial function supplies the communication rule of the CCS operational semantics.
