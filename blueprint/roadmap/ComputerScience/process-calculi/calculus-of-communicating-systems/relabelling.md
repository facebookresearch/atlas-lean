# Relabelling

A finite CCS relabelling over channel names is a finite list of entries
$(a, \ell)$, each pairing a channel name $a$ with a visible label $\ell$, that is, an input or an
output on some channel. The entry $(a, \ell)$ gives $\ell$ as the image of the input on $a$; the
image of the output on $a$ is then the complement of $\ell$. The first entry with name $a$ is
used, and a name occurring in no entry is mapped to itself.
