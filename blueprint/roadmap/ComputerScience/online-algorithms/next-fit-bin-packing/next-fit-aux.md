# Next Fit Aux

Next Fit bin packing with unit bins: scan the items keeping the
current bin's load; when the next item does not fit, close the bin
and start a new one. `nextFitAux items bins load` processes `items`
given `bins` bins already started and current load `load`.
