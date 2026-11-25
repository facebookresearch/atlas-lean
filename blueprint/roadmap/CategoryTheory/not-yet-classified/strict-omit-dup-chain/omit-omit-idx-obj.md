# Omit Omit idx obj

Pointwise `δδ` index equality: omitting `j.succ` then `i` agrees with
omitting `j` then `i.castSucc`, for `i ≤ j`. The first rewrite swaps the
omission order via `Fin.succAbove_succAbove_succAbove_predAbove`; the two
bridges collapse the swapped indices via `Fin.succAbove_succ_of_le` and
`Fin.predAbove_succ_of_le`.
