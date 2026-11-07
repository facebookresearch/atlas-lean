# List update problem

## Costs

- [Access cost](access-cost.md)
- [Move-to-front](mtf.md)
- [Cost of move-to-front](mtf-cost.md)
- [Final list of move-to-front](mtf-final.md)
- [Inversion set of two lists](inv-set.md)
- [Number of inversions between two lists](inv.md)
- [Offline cost without free exchanges](offline-cost.md)
- [Free move](free-move.md)
- [Offline cost with free exchanges](offline-cost-free.md)

## Order facts

- [Indices after erasing an entry](idx-of-erase.md)
- [Move-to-front keeps the relative order of the other items](idx-of-mtf-lt-iff.md)
- [Counting the entries before an entry](card-before.md)

## The potential: inversions against the offline list

- [Members of the inversion set](mem-of-mem-inv-set.md)
- [Triangle inequality for inversions](inv-triangle.md)
- [The amortized cost of a move-to-front step](mtf-step.md)

## Move-to-front is `2`-competitive

- [Move-to-front rearranges the list](mtf-perm.md)

## Free exchanges

- [A free move rearranges the list](free-move-perm.md)
- [Free moves never add inversions against a list headed by the moved item](inv-free-move-le.md)
- [Amortized bound for move-to-front over a request sequence, with free exchanges](mtf-cost-add-inv-le-free.md)
- [Without free moves the two offline costs agree](offline-cost-free-no-move.md)
- [Amortized bound for move-to-front over a request sequence](mtf-cost-add-inv-le.md)
- [Move-to-front is 2-competitive](mtf-cost-le-free.md)
- [Move-to-front is 2-competitive without free exchanges](mtf-cost-le.md)
- [Move-to-front against a static list](mtf-cost-le-static.md)

## The lower bound for deterministic online algorithms

- [Deterministic online list-update algorithm](deterministic-online-list-update-algorit.md)
- [Cost of an online list-update algorithm](cost.md)
- [The list-update adversary](adversary.md)
- [The list of an algorithm on a nonempty list is never empty](list-ne-nil.md)
- [The adversary makes every access cost the full length of the list](cost-adversary.md)
- [Online move-to-front](mtf-online.md)
- [Online move-to-front pays the move-to-front cost](mtf-online-cost.md)
- [Static cost](static-cost.md)
- [The static cost is the offline cost of a constant list](offline-cost-const.md)
- [Positions in a list and in its reverse](access-cost-add-reverse.md)
- [A list or its reverse serves any sequence at average cost at most $(\ell + 1)/2$](static-cost-add-reverse.md)
- [Inversions are at most the squared length](inv-le-sq.md)
- [Switching lists after the first request](offline-cost-switch-le.md)
- [Online and offline costs on the adversary's sequence](adversary-vs-offline.md)
- [No deterministic online list-update algorithm beats $2 - 2/(\ell + 1)$](not-competitive.md)
