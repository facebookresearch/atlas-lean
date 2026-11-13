# Gap cost

Given an integer gap-open cost $o$, an integer gap-extend cost $e$ and gap states
$p$ (of the previous column) and $c$ (of the current gap column), the cost of the current column
is $e$ if $p = c$ (the column continues a run) and $o$ otherwise (it opens a run).
