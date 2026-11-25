# Joint distribution of the re-shared subshares seen by a coalition

Let `F` be a field and `Party` a finite type of parties with decidable
equality, with Shamir parameters `params` and a tail sampler `sampler`. For a
coalition `I` and values `h : Party → F`, `dealerViews params sampler I h` is
the distribution on matrices `Party → I → F` received by `I` when every dealer
`i` re-shares `h i` by Shamir sharing with fresh independent randomness.
