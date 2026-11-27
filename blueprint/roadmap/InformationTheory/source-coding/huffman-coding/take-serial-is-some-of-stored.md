# A stored work item can be removed by its serial

Let $t$ be a table of optional Huffman
work items and let $w$ be a work item with serial number $s$. If the entry of $t$ at index $s$
is $w$, then removing serial $s$ from $t$ succeeds and returns the tree of $w$ together with an
updated table.
