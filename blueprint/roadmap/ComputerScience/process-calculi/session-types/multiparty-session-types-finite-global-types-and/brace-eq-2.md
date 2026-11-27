# Brace equality of local branch lists

Let participants, payload sorts and labels have decidable equality. Brace equality of local branch lists compares the entries of the first list in order: each entry is compared with the first remaining entry of the second list carrying the same label, which must exist and be brace-equal and is then removed. The lists are brace-equal when every entry is matched in this way and nothing of the second list remains.
