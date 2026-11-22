# Restriction of a binary decision diagram

For a variable $x$ and a Boolean $b$, the
restriction (cofactor) $t[x := b]$ of a binary decision diagram $t$ is defined recursively: a
leaf is kept; a node testing $x$ is replaced by the restriction of its $\mathrm{hi}$ child if $b$
is true and of its $\mathrm{lo}$ child if $b$ is false; and a node testing any other variable
$v$ is rebuilt from the restrictions of its two children with the reducing node constructor,
which returns the common child when the two are equal and a node testing $v$ otherwise.
