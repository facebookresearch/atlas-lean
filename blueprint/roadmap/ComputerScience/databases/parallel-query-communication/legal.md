# Legal initial placements for query communication

For a public worker count and a fixed vector of relation lengths, give each worker a number of local slots. The counts at any two workers differ by at most one. A bijection assigns to each worker/slot pair a relation/offset pair, so each raw input position occurs exactly once. The wiring contains no payload bits. Varying those bits while holding the wiring fixed changes slot contents only at positions wired to them.
