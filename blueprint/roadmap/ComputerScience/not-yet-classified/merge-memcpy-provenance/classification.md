# Classification

Each declared site is classified exclusively by its physical backing
relationship: all `memcpy` sites have proved-distinct backings, while all
same-store sites carry one of the four memmove tags.
