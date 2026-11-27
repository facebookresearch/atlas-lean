# Strong MAC forgery experiment

The strong forgery experiment (Katz and Lindell, Definition 4.3) runs like
$\mathrm{Mac}\text{-}\mathrm{forge}$, but the forgery $(m, t)$ wins when it verifies and the oracle
never answered a query $m$ with the tag $t$: a new tag on a queried message counts as a forgery.
